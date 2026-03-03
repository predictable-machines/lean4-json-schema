import Lean
import JsonSchema.Schema

namespace JsonSchema.Derive

open Lean Elab Command Meta

-- Check whether an Expr transitively mentions a given constant (used for recursion detection)
def exprContainsConst (e : Expr) (n : Name) : Bool :=
  match e with
  | .const c _     => c == n
  | .app f a       => exprContainsConst f n || exprContainsConst a n
  | .lam _ t b _   => exprContainsConst t n || exprContainsConst b n
  | .forallE _ t b _ => exprContainsConst t n || exprContainsConst b n
  | .letE _ t v b _ => exprContainsConst t n || exprContainsConst v n || exprContainsConst b n
  | .mdata _ e     => exprContainsConst e n
  | .proj _ _ e    => exprContainsConst e n
  | _              => false

/-- Collect Sort-valued (Type, Type u, etc.) parameter names and build the applied
    type syntax `DeclName α β ...` for polymorphic instances. -/
def getPolyParams (declName : Name) (indVal : InductiveVal)
    : CommandElabM (Array Name × TSyntax `term) := do
  let declId := mkIdent declName
  if indVal.numParams == 0 then
    return (#[], declId)
  liftTermElabM <| forallTelescopeReducing indVal.type fun xs _ => do
    let mut paramNames : Array Name := #[]
    let mut paramIdents : Array (TSyntax `term) := #[]
    for i in [:indVal.numParams] do
      let param := xs[i]!
      let paramType ← inferType param
      unless paramType.isSort do continue
      let paramName ← param.fvarId!.getUserName
      paramNames := paramNames.push paramName
      paramIdents := paramIdents.push (mkIdent paramName)
    let appliedType ← if paramIdents.isEmpty then
      `(term| $declId)
    else
      `(term| $declId $paramIdents*)
    return (paramNames, appliedType)

/-- Emit `section` + `variable` commands for each type parameter, adding the
    given class constraints. Call `closePolySection` after elaborating the instance. -/
def openPolySection (paramNames : Array Name) (classes : Array Name)
    : CommandElabM Unit := do
  if paramNames.isEmpty then return
  elabCommand (← `(command| section))
  for paramName in paramNames do
    let paramIdent := mkIdent paramName
    elabCommand (← `(command| variable {$paramIdent : Type}))
    for cls in classes do
      let clsIdent := mkIdent cls
      elabCommand (← `(command| variable [$clsIdent $paramIdent]))

def closePolySection (paramNames : Array Name) : CommandElabM Unit := do
  if paramNames.isEmpty then return
  elabCommand (← `(command| end))

/-- Pre-computed analysis of an inductive type, shared between the HasJSONSchema
    and ValidatesAgainstSchema derive handlers to avoid duplicating constructor
    iteration, arg counting, recursion detection, and polymorphism analysis. -/
structure CtorAnalysis where
  indVal : InductiveVal
  ctorInfos : List ConstructorVal
  argCounts : List Nat
  zeroArgCtorNames : Array String
  isRecursive : Bool
  -- True when a constructor arg is recursive but wrapped (e.g. `List Self`, `String × Self`).
  -- Lean's `deriving ToJson` produces `partial` defs for these, making proofs impossible.
  hasWrappedRecursion : Bool
  paramNames : Array Name
  appliedType : TSyntax `term

def CtorAnalysis.hasZeroArgs (a : CtorAnalysis) : Bool := !a.zeroArgCtorNames.isEmpty
def CtorAnalysis.hasArgCarrying (a : CtorAnalysis) : Bool := a.argCounts.any (· > 0)

/-- Analyze a non-structure inductive type: collect constructor metadata, detect
    recursion, and compute polymorphism info. Returns `none` for structures or
    non-inductive types. Both derive handlers call this once instead of
    independently computing the same information. -/
def analyzeInductive (declName : Name) : CommandElabM (Option CtorAnalysis) := do
  let env ← getEnv
  if isStructure env declName then return none
  let some constInfo := env.find? declName | return none
  let .inductInfo indVal := constInfo | return none

  let ctorInfos ← indVal.ctors.mapM fun ctorName => getConstInfoCtor ctorName
  let argCounts ← ctorInfos.mapM fun ctorInfo =>
    liftTermElabM <| forallTelescopeReducing ctorInfo.type fun xs _ =>
      pure (xs.size - indVal.numParams)

  let zeroArgCtorNames := (ctorInfos.zip argCounts).filterMap fun (ci, n) =>
    if n == 0 then some ci.name.getString! else none

  let mut isRecursive := false
  let mut hasWrappedRecursion := false
  for (ctorInfo, numArgs) in ctorInfos.zip argCounts do
    if numArgs == 0 then continue
    let (hasRec, hasWrapped) ← liftTermElabM <|
      forallTelescopeReducing ctorInfo.type fun xs _ => do
        let mut foundRec := false
        let mut foundWrapped := false
        for i in [:numArgs] do
          let argType ← inferType xs[indVal.numParams + i]!
          if exprContainsConst argType declName then
            foundRec := true
            -- Wrapped recursion: arg type contains `declName` but is not `declName` itself
            -- (e.g., `List Self` or `String × Self` rather than bare `Self`).
            unless argType.isAppOf declName do foundWrapped := true
        pure (foundRec, foundWrapped)
    if hasRec then isRecursive := true
    if hasWrapped then hasWrappedRecursion := true

  let (paramNames, appliedType) ← getPolyParams declName indVal
  return some {
    indVal, ctorInfos, argCounts,
    zeroArgCtorNames := zeroArgCtorNames.toArray,
    isRecursive, hasWrappedRecursion, paramNames, appliedType
  }

def mkEnumHasJSONSchemaInstanceCmd (declName : Name) : CommandElabM Bool := do
  let some analysis ← analyzeInductive declName | return false
  -- Pure enums: every constructor is zero-arg
  if analysis.hasArgCarrying then return false

  openPolySection analysis.paramNames #[``HasJSONSchema]
  let enumValues := analysis.indVal.ctors.map fun ctorName => ctorName.getString!
  let enumValuesStx ← enumValues.toArray.mapM fun val => `(term| $(Syntax.mkStrLit val))

  let cmd ← `(command|
    instance : HasJSONSchema $(analysis.appliedType) where
      toSchema := stringSchema (enum := some [$enumValuesStx,*])
  )
  elabCommand cmd
  closePolySection analysis.paramNames
  return true

def mkStructHasJSONSchemaInstanceCmd (declName : Name) : CommandElabM Bool := do
  let env ← getEnv

  unless (isStructure env declName) do
    return false

  let indVal ← getConstInfoInduct declName

  let fieldNames := getStructureFieldsFlattened env declName (includeSubobjectFields := false)

  let ctorInfo ← getConstInfoCtor indVal.ctors[0]!

  let (paramNames, appliedType) ← getPolyParams declName indVal
  openPolySection paramNames #[``HasJSONSchema]

  let cmd ← liftTermElabM do
    forallTelescopeReducing ctorInfo.type fun xs _ => do
      let numParams := indVal.numParams

      if xs.size != numParams + fieldNames.size then
        throwError "'deriving HasJSONSchema' failed, unexpected number of fields in structure"

      let fieldSchemas ← fieldNames.mapIdxM fun i fieldName => do
        let fieldStr := fieldName.toString
        let x := xs[numParams + i]!
        let fieldType ← inferType x
        let fieldTypeStx ← PrettyPrinter.delab fieldType

        `(term| ($(Syntax.mkStrLit fieldStr), @HasJSONSchema.toSchema $fieldTypeStx _))

      let requiredFields ← fieldNames.mapM fun fieldName => do
        `(term| $(Syntax.mkStrLit (fieldName.toString)))

      `(command|
        instance : HasJSONSchema $appliedType where
          toSchema := objectSchema [$fieldSchemas,*] [$requiredFields,*]
      )

  elabCommand cmd
  closePolySection paramNames
  return true

/-- Generate a schema term for a type that may contain recursive references to `declName`.
    Decomposes wrapper types (List, Array, Option, Prod) to preserve their schema structure,
    using `anySchema` only at leaf positions where the type is directly the recursive type.
    Without this, `List TypeExpr` would collapse to just `$ref` instead of
    `{"type":"array","items":{"$ref":"..."}}`. -/
partial def mkSchemaTermForType (argType : Expr) (declName : Name)
    : TermElabM (TSyntax `term) := do
  -- Direct recursive reference: type's head IS the type being defined
  if argType.getAppFn.isConstOf declName then
    let refNameStx := Syntax.mkStrLit declName.getString!
    return (← `(term| anySchema (refName := some $refNameStx)))
  -- List α → arraySchema (<recurse on α>)
  if argType.getAppFn.isConstOf ``List then
    let args := argType.getAppArgs
    if args.size == 1 && exprContainsConst args[0]! declName then
      let inner ← mkSchemaTermForType args[0]! declName
      return (← `(term| arraySchema $inner))
  -- Array α → arraySchema (<recurse on α>)
  if argType.getAppFn.isConstOf ``Array then
    let args := argType.getAppArgs
    if args.size == 1 && exprContainsConst args[0]! declName then
      let inner ← mkSchemaTermForType args[0]! declName
      return (← `(term| arraySchema $inner))
  -- Option α → oneOfSchema [<recurse on α>, nullSchema]
  if argType.getAppFn.isConstOf ``Option then
    let args := argType.getAppArgs
    if args.size == 1 && exprContainsConst args[0]! declName then
      let inner ← mkSchemaTermForType args[0]! declName
      return (← `(term| oneOfSchema [$inner, nullSchema]))
  -- Prod α β → tupleSchema [<recurse on α>, <recurse on β>]
  if argType.getAppFn.isConstOf ``Prod then
    let args := argType.getAppArgs
    if args.size == 2 && (exprContainsConst args[0]! declName ||
                          exprContainsConst args[1]! declName) then
      let left ← mkSchemaTermForType args[0]! declName
      let right ← mkSchemaTermForType args[1]! declName
      return (← `(term| tupleSchema [$left, $right]))
  -- Non-recursive leaf: delegate to existing HasJSONSchema instance
  let argTypeStx ← PrettyPrinter.delab argType
  `(term| @HasJSONSchema.toSchema $argTypeStx _)

/-- Handles inductives with at least one argument-carrying constructor.
    Zero-arg constructors are grouped into a string-enum entry; single-arg
    constructors become `{"type":"object","properties":{...}}` entries;
    multi-arg constructors use `tupleSchema` for positional validation.
    Recursive positions are decomposed by `mkSchemaTermForType` to preserve
    wrapper structure (List, Array, Option, Prod) around `$ref` pointers. -/
def mkInductiveHasJSONSchemaInstanceCmd (declName : Name) : CommandElabM Bool := do
  let some analysis ← analyzeInductive declName | return false
  unless analysis.hasArgCarrying do return false

  openPolySection analysis.paramNames #[``HasJSONSchema]

  let mut schemaTerms : Array (TSyntax `term) := #[]

  for (ctorInfo, numArgs) in analysis.ctorInfos.zip analysis.argCounts do
    if numArgs == 0 then continue
    let ctorShortName := ctorInfo.name.getString!
    let term ← liftTermElabM <|
      forallTelescopeReducing ctorInfo.type fun xs _ => do
        let keyStx := Syntax.mkStrLit ctorShortName
        -- Lean's `deriving ToJson` encoding depends on whether constructor args
        -- are explicitly named:
        --   Named   `| foo (x : Nat) (y : String)` → `{"foo": {"x": 1, "y": "hi"}}`
        --   Unnamed `| foo : Nat → String → T`      → `{"foo": [1, "hi"]}` or `{"foo": 5}`
        -- Detect via Name.isInternal on the first arg's binder name.
        let firstArgName ← xs[analysis.indVal.numParams]!.fvarId!.getUserName
        let hasNamedArgs := !firstArgName.isInternal
        if hasNamedArgs then
          -- Named args: inner objectSchema with field names matching ToJson encoding
          let mut fieldSchemas : Array (TSyntax `term) := #[]
          let mut fieldNames : Array (TSyntax `term) := #[]
          for i in [:numArgs] do
            let param := xs[analysis.indVal.numParams + i]!
            let fieldName := (← param.fvarId!.getUserName).toString
            let fieldNameStx := Syntax.mkStrLit fieldName
            let argType ← inferType param
            let schemaTerm ← mkSchemaTermForType argType declName
            fieldSchemas := fieldSchemas.push (← `(term| ($fieldNameStx, $schemaTerm)))
            fieldNames := fieldNames.push fieldNameStx
          let innerSchema ← `(term| objectSchema [$fieldSchemas,*] [$fieldNames,*])
          `(term| objectSchema [($keyStx, $innerSchema)] [$keyStx])
        else if numArgs == 1 then
          -- Unnamed single arg: direct value (e.g., `{"minLength": 5}`)
          let argType ← inferType xs[analysis.indVal.numParams]!
          let schemaTerm ← mkSchemaTermForType argType declName
          `(term| objectSchema [($keyStx, $schemaTerm)] [$keyStx])
        else
          -- Unnamed multi args: positional tuple (e.g., `{"foo": [1, "hi"]}`)
          let mut argSchemaTerms : Array (TSyntax `term) := #[]
          for i in [:numArgs] do
            let argType ← inferType xs[analysis.indVal.numParams + i]!
            argSchemaTerms := argSchemaTerms.push
              (← mkSchemaTermForType argType declName)
          `(term| objectSchema [($keyStx, tupleSchema [$argSchemaTerms,*])] [$keyStx])
    schemaTerms := schemaTerms.push term

  -- Zero-arg constructors are grouped as a single string-enum entry in the oneOf
  let allSchemaTerms ← if !analysis.hasZeroArgs then
    pure schemaTerms
  else do
    let enumVals ← analysis.zeroArgCtorNames.mapM fun val =>
      `(term| $(Syntax.mkStrLit val))
    let enumTerm ← `(term| stringSchema (enum := some [$enumVals,*]))
    pure (#[enumTerm] ++ schemaTerms)

  let cmd ← if analysis.isRecursive then do
    let refNameStx := Syntax.mkStrLit declName.getString!
    `(command|
      instance : HasJSONSchema $(analysis.appliedType) where
        toSchema := oneOfSchema [$allSchemaTerms,*] (refName := some $refNameStx)
    )
  else
    `(command|
      instance : HasJSONSchema $(analysis.appliedType) where
        toSchema := oneOfSchema [$allSchemaTerms,*]
    )
  elabCommand cmd
  closePolySection analysis.paramNames
  return true

def mkHasJSONSchemaInstanceCmd (declName : Name) : CommandElabM Bool := do
  if ← mkEnumHasJSONSchemaInstanceCmd declName then
    return true

  if ← mkStructHasJSONSchemaInstanceCmd declName then
    return true

  if ← mkInductiveHasJSONSchemaInstanceCmd declName then
    return true

  return false

def hasJSONSchemaHandler (declNames : Array Name) : CommandElabM Bool := do
  let mut succeeded := false
  for declName in declNames do
    if ← mkHasJSONSchemaInstanceCmd declName then
      succeeded := true
    else
      logInfo m!"Could not derive HasJSONSchema for {declName}"
  unless succeeded do
    throwError "Could not derive HasJSONSchema for any of the types"
  return succeeded

end JsonSchema.Derive

initialize
  Lean.Elab.registerDerivingHandler ``JsonSchema.HasJSONSchema JsonSchema.Derive.hasJSONSchemaHandler
