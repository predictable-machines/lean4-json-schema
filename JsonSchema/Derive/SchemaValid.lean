import Lean
import PredictableJsonSchema.Schema
import PredictableJsonSchema.Validation
import PredictableJsonSchema.Correctness.Soundness
import PredictableJsonSchema.Correctness.Bridge
import PredictableJsonSchema.Correctness.ValidatesAgainstSchema
import PredictableJsonSchema.Derive.Schema

namespace JsonSchema.Derive

open Lean Elab Command Meta

/-- Generate `ValidatesAgainstSchema` for a pure enum (all zero-arg constructors).
    Proof: case-split + native_decide (everything is concrete after case split). -/
def mkEnumValidatesInstanceCmd (declName : Name) : CommandElabM Bool := do
  let some analysis ← analyzeInductive declName | return false
  if analysis.hasArgCarrying then return false

  openPolySection analysis.paramNames
    #[``HasJSONSchema, ``Lean.ToJson, ``ValidatesAgainstSchema]
  let cmd ← `(command|
    instance : ValidatesAgainstSchema $(analysis.appliedType) where
      valid c := by cases c <;> native_decide
  )
  elabCommand cmd
  closePolySection analysis.paramNames
  return true

/-- Generate `ValidatesAgainstSchema` for a structure.
    Uses `validateJson_mkObj_objectSchema` bridge theorem with `show` to normalize
    the List.flatten from derived ToJson. -/
def mkStructValidatesInstanceCmd (declName : Name) : CommandElabM Bool := do
  let env ← getEnv
  unless isStructure env declName do return false

  let indVal ← getConstInfoInduct declName
  let fieldNames := getStructureFieldsFlattened env declName (includeSubobjectFields := false)
  let ctorInfo ← getConstInfoCtor indVal.ctors[0]!

  let (paramNames, appliedType) ← getPolyParams declName indVal
  openPolySection paramNames
    #[``HasJSONSchema, ``Lean.ToJson, ``ValidatesAgainstSchema]

  let cmd ← liftTermElabM do
    forallTelescopeReducing ctorInfo.type fun xs _ => do
      let numParams := indVal.numParams

      if xs.size != numParams + fieldNames.size then
        throwError "'deriving ValidatesAgainstSchema' failed, unexpected number of fields"

      -- Build prop entries: [("f", @HasJSONSchema.toSchema T _), ...]
      let propEntries ← fieldNames.mapIdxM fun i fieldName => do
        let x := xs[numParams + i]!
        let fieldType ← inferType x
        let fieldTypeStx ← PrettyPrinter.delab fieldType
        `(term| ($(Syntax.mkStrLit (fieldName.toString)),
                 @HasJSONSchema.toSchema $fieldTypeStx _))

      -- Build pair entries: [("f", toJson a.f), ...]
      let pairEntries ← fieldNames.mapM fun fieldName => do
        let fieldId := mkIdent fieldName
        `(term| ($(Syntax.mkStrLit (fieldName.toString)), toJson (a.$fieldId)))

      -- Build required key list: ["f", ...]
      let reqEntries ← fieldNames.mapM fun fieldName =>
        `(term| $(Syntax.mkStrLit (fieldName.toString)))

      -- Build hValid tactic: sequential rcases peeling off one field at a time
      let n := fieldNames.size
      let mut hValidTactics : Array (TSyntax `tactic) := #[]
      hValidTactics := hValidTactics.push
        (← `(tactic| intro name schema hns v hv))
      hValidTactics := hValidTactics.push
        (← `(tactic| simp only [List.mem_cons, Prod.mk.injEq,
                                 List.mem_nil_iff, or_false] at hns))
      -- Peel off one field at a time; simp_all closes the substituted branch
      for _ in [:(n - 1)] do
        hValidTactics := hValidTactics.push
          (← `(tactic| rcases hns with ⟨rfl, rfl⟩ | hns <;>
                 try simp_all [ValidatesAgainstSchema.valid]))
      -- Final field (try-wrapped: may already be solved for small n)
      hValidTactics := hValidTactics.push
        (← `(tactic| try obtain ⟨rfl, rfl⟩ := hns))
      hValidTactics := hValidTactics.push
        (← `(tactic| try simp_all [ValidatesAgainstSchema.valid]))

      `(command|
        instance : ValidatesAgainstSchema $appliedType where
          valid a := by
            show validateJson
              (objectSchema [$propEntries,*] [$reqEntries,*])
              (Json.mkObj [$pairEntries,*]) = .ok ()
            exact validateJson_mkObj_objectSchema _ _ _
              (by simp only [List.map]; decide)
              (hReq_of_map_fst _ _ rfl)
              (by intro k hk; simp only [List.map] at hk ⊢; exact hk)
              (by $hValidTactics*)
      )

  elabCommand cmd
  closePolySection paramNames
  return true

/-- Generate a proof term that proves `validateJson schema (toJson x) = .ok ()` for
    a constructor argument type that may wrap the recursive type in List/Array/Option/Prod.
    Mirrors `mkSchemaTermForType`: at each wrapper layer, generates the appropriate
    bridge theorem application; at recursive leaves uses `validateJson_anySchema`;
    at non-recursive leaves uses `ValidatesAgainstSchema.valid`. -/
partial def mkValidationProofTerm (argType : Expr) (declName : Name)
    : TermElabM (TSyntax `term) := do
  -- Direct recursive: anySchema validates anything
  if argType.getAppFn.isConstOf declName then
    return (← `(term| by simp))
  -- List α where α transitively contains declName
  if argType.getAppFn.isConstOf ``List then
    let args := argType.getAppArgs
    if args.size == 1 && exprContainsConst args[0]! declName then
      let innerProof ← mkValidationProofTerm args[0]! declName
      -- Each item validates against the inner schema; compose via validateArrayItems_of_forall
      return (← `(term| by
        simp only [toJson, List.toJson, Array.toJson, validateJson,
          arraySchema, Array.toList_map]
        exact validateArrayItems_of_forall _ _ (fun a _ => $innerProof) 0))
  -- Array α where α transitively contains declName
  if argType.getAppFn.isConstOf ``Array then
    let args := argType.getAppArgs
    if args.size == 1 && exprContainsConst args[0]! declName then
      let innerProof ← mkValidationProofTerm args[0]! declName
      return (← `(term| by
        simp only [toJson, Array.toJson, validateJson,
          arraySchema, Array.toList_map]
        exact validateArrayItems_of_forall _ _ (fun a _ => $innerProof) 0))
  -- Option α where α transitively contains declName
  if argType.getAppFn.isConstOf ``Option then
    let args := argType.getAppArgs
    if args.size == 1 && exprContainsConst args[0]! declName then
      let innerProof ← mkValidationProofTerm args[0]! declName
      return (← `(term| by
        cases ‹_› with
        | some val =>
          simp only [toJson, Option.toJson]
          exact validateJson_oneOfSchema_correct _ _ _ (List.Mem.head _) $innerProof
        | none =>
          simp only [toJson, Option.toJson]
          exact validateJson_oneOfSchema_correct _ _ _
            (List.Mem.tail _ (List.Mem.head _)) validateJson_nullSchema))
  -- Prod α β where either transitively contains declName.
  -- The proof term references `_x` — always in scope because Prod args only
  -- appear in single-arg constructors, which bind `next _x => ...`.
  if argType.getAppFn.isConstOf ``Prod then
    let args := argType.getAppArgs
    if args.size == 2 && (exprContainsConst args[0]! declName ||
                          exprContainsConst args[1]! declName) then
      let leftProof ← mkValidationProofTerm args[0]! declName
      let rightProof ← mkValidationProofTerm args[1]! declName
      return (← `(term| by
        show validateJson _ (Json.arr #[toJson _x.1, toJson _x.2]) = .ok ()
        exact validateJson_tupleSchema_pair _ _ _ _ $leftProof $rightProof))
  -- Non-recursive leaf: delegate to ValidatesAgainstSchema instance
  `(term| ValidatesAgainstSchema.valid _)

/-- Build a `List.Mem` proof term for position `idx` in a list.
    Position 0 → `List.Mem.head _`, position k → `List.Mem.tail _ (... (List.Mem.head _))`. -/
private def mkMemProof (idx : Nat) : CommandElabM (TSyntax `term) := do
  let mut term ← `(term| List.Mem.head _)
  for _ in [:idx] do
    term ← `(term| List.Mem.tail _ $term)
  return term

/-- Build the `have _inner` bridge proof for an arg-carrying constructor.
    The first 3 arguments to validateJson_mkObj_objectSchema are identical boilerplate
    for all single-key object schemas; this helper factors them out. -/
private def mkObjBridgeHave
    (objSchema jsonValue : TSyntax `term)
    (hValidBody : Array (TSyntax `tactic))
    : CommandElabM (TSyntax `tactic) :=
  `(tactic|
    have _inner : validateJson ($objSchema) ($jsonValue) = .ok () :=
      validateJson_mkObj_objectSchema _ _ _
        (by simp only [List.map]; decide)
        (hReq_of_map_fst _ _ rfl)
        (by intro k hk; simp only [List.map] at hk ⊢; exact hk)
        (by $hValidBody*))

/-- Build the hValid callback for multi-arg (≥2) constructors.
    Unpacks the single-field object, then applies the appropriate arity-specific
    tuple bridge theorem (pair/triple/quad corollaries of `validateJson_tupleSchema`).
    For 2-arg, includes an extra `show` to normalize Prod encoding to Json.arr.
    The arity-specific corollaries are used instead of the general theorem because
    the proof terms may be tactic blocks (`by simp` for recursive args), which need
    the theorem parameter to provide type context — `have x := by simp` without a
    type annotation leaves Lean with no goal to reduce. -/
-- Arity limit: constructors with > 4 arguments are not supported by the derive
-- handlers. Both `HasJSONSchema` and `ValidatesAgainstSchema` encode multi-arg
-- constructors as tuples and need per-arity bridge theorems (pair/triple/quad).
-- Extending beyond 4 requires adding new tuple validation theorems in Soundness.lean.
private def mkTupleHValid (numArgs : Nat) (proofs : Array (TSyntax `term))
    : CommandElabM (Array (TSyntax `tactic)) := do
  let tupleExact ← match numArgs with
    | 2 => `(tactic| exact validateJson_tupleSchema_pair _ _ _ _
              $(proofs[0]!) $(proofs[1]!))
    | 3 => `(tactic| exact validateJson_tupleSchema_triple _ _ _ _ _ _
              $(proofs[0]!) $(proofs[1]!) $(proofs[2]!))
    | 4 => `(tactic| exact validateJson_tupleSchema_quad _ _ _ _ _ _ _ _
              $(proofs[0]!) $(proofs[1]!) $(proofs[2]!) $(proofs[3]!))
    | _ => throwError "'deriving ValidatesAgainstSchema' unsupported: >4 constructor args"
  let mut tacs : Array (TSyntax `tactic) := #[]
  tacs := tacs.push (← `(tactic| intro name schema hns v hv))
  tacs := tacs.push (← `(tactic|
      simp only [List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at hns hv))
  tacs := tacs.push (← `(tactic| obtain ⟨h1, h2⟩ := hns))
  tacs := tacs.push (← `(tactic| subst h1))
  tacs := tacs.push (← `(tactic| subst h2))
  tacs := tacs.push (← `(tactic| obtain ⟨-, h3⟩ := hv))
  tacs := tacs.push (← `(tactic| subst h3))
  if numArgs == 2 then
    tacs := tacs.push (← `(tactic|
        show validateJson _ (Json.arr #[toJson _x, toJson _y]) = .ok ()))
  tacs := tacs.push tupleExact
  return tacs

/-- Like `mkObjBridgeHave` but binds to `_namedObj` instead of `_inner`.
    Used for the inner objectSchema proof in named-arg constructors, where the
    outer object wraps an inner object of named fields. -/
private def mkNamedObjBridgeHave
    (objSchema jsonValue : TSyntax `term)
    (hValidBody : Array (TSyntax `tactic))
    : CommandElabM (TSyntax `tactic) :=
  `(tactic|
    have _namedObj : validateJson ($objSchema) ($jsonValue) = .ok () :=
      validateJson_mkObj_objectSchema _ _ _
        (by simp only [List.map]; decide)
        (hReq_of_map_fst _ _ rfl)
        (by intro k hk; simp only [List.map] at hk ⊢; exact hk)
        (by $hValidBody*))

/-- Build the hValid callback for named-arg constructors' inner objectSchema.
    Peels one field at a time (like the struct handler). Each branch uses `first`
    with a fallback to the precomputed proof from `mkValidationProofTerm`,
    supporting both non-recursive fields (closed by `simp_all`) and recursive
    fields (closed by `exact $proof`). -/
private def mkNamedArgsInnerHValid (numFields : Nat) (proofs : Array (TSyntax `term))
    : CommandElabM (Array (TSyntax `tactic)) := do
  let mut tacs : Array (TSyntax `tactic) := #[]
  tacs := tacs.push (← `(tactic| intro name schema hns v hv))
  tacs := tacs.push (← `(tactic|
      simp only [List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at hns))
  for i in [:(numFields - 1)] do
    let fieldProof := proofs[i]!
    tacs := tacs.push (← `(tactic|
      rcases hns with ⟨rfl, rfl⟩ | hns <;>
        try first
          | (simp_all [ValidatesAgainstSchema.valid]; done)
          | (simp_all only [List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false]
             exact $fieldProof)))
  -- Final field
  let lastProof := proofs[numFields - 1]!
  tacs := tacs.push (← `(tactic| try obtain ⟨rfl, rfl⟩ := hns))
  tacs := tacs.push (← `(tactic|
    try first
      | (simp_all [ValidatesAgainstSchema.valid]; done)
      | (simp_all only [List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false]
         exact $lastProof)))
  return tacs

/-- Build the hValid callback for the outer objectSchema of a named-arg constructor.
    The outer object has exactly one property (the constructor name). After deconstructing
    the membership hypotheses, the goal reduces to `_namedObj` (the inner proof bound by
    `mkNamedObjBridgeHave`). -/
private def mkNamedArgsOuterHValid : CommandElabM (Array (TSyntax `tactic)) := do
  pure #[
    ← `(tactic| intro name schema hns v hv),
    ← `(tactic|
        simp only [List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at hns hv),
    ← `(tactic| obtain ⟨h1, h2⟩ := hns),
    ← `(tactic| subst h1),
    ← `(tactic| subst h2),
    ← `(tactic| obtain ⟨-, h3⟩ := hv),
    ← `(tactic| subst h3),
    ← `(tactic| exact _namedObj)]

/-- Generate `ValidatesAgainstSchema` for an inductive with arg-carrying constructors.
    Proof strategies per constructor:
    - Zero-arg: `native_decide` (fully concrete)
    - Named-arg (any arity): nested `validateJson_mkObj_objectSchema` for both outer
      and inner objectSchemas, with `_namedObj` binding the inner proof
    - Unnamed single-arg: `validateJson_oneOfSchema_correct` + `validateJson_mkObj_objectSchema`
    - Unnamed multi-arg: same outer structure + `validateJson_tupleSchema_pair/triple/quad` -/
def mkInductiveValidatesInstanceCmd (declName : Name) : CommandElabM Bool := do
  let some analysis ← analyzeInductive declName | return false
  unless analysis.hasArgCarrying do return false

  if analysis.hasWrappedRecursion then
    logInfo m!"Note: '{declName}' has wrapped-recursive constructor args (e.g., List {declName} \
      or Prod containing {declName}). Lean's `deriving ToJson` produces a `partial` def for such \
      types, which is kernel-opaque and may cause the proof to fail. If so, write a manual \
      non-partial `ToJson` instance."

  openPolySection analysis.paramNames
    #[``HasJSONSchema, ``Lean.ToJson, ``ValidatesAgainstSchema]

  -- Build the full oneOf schema term list (mirrors mkInductiveHasJSONSchemaInstanceCmd).
  -- argCarryingSchemas/Proofs store per-arg-carrying constructor data for the proof loop.
  let mut schemaTerms : Array (TSyntax `term) := #[]
  let mut argCarryingSchemas : Array (TSyntax `term) := #[]
  let mut argCarryingProofs : Array (Array (TSyntax `term)) := #[]
  -- For named-arg constructors: some (innerObjectSchema, fieldNames).
  -- none for unnamed-arg constructors. Mirrors the `hasNamedArgs` check in Schema.lean.
  let mut argCarryingNamedInfo : Array (Option (TSyntax `term × Array String)) := #[]
  if analysis.hasZeroArgs then
    let enumVals ← analysis.zeroArgCtorNames.mapM fun val =>
      `(term| $(Syntax.mkStrLit val))
    schemaTerms := schemaTerms.push (← `(term| stringSchema (enum := some [$enumVals,*])))

  for (ctorInfo, numArgs) in analysis.ctorInfos.zip analysis.argCounts do
    if numArgs == 0 then continue
    let ctorShortName := ctorInfo.name.getString!
    let (ctorSchema, proofs, namedInfo) ← liftTermElabM <|
      forallTelescopeReducing ctorInfo.type fun xs _ => do
      let keyStx := Syntax.mkStrLit ctorShortName
      -- Detect named vs unnamed args (same heuristic as Schema.lean).
      -- Lean doesn't allow mixing named and unnamed binders in a single constructor,
      -- so checking only the first arg is sufficient.
      let firstArgName ← xs[analysis.indVal.numParams]!.fvarId!.getUserName
      let hasNamedArgs := !firstArgName.isInternal
      if hasNamedArgs then
        -- Named args: inner objectSchema with field names matching ToJson encoding.
        -- ToJson encodes `| ctor (f1 : T1) (f2 : T2)` as `{"ctor": {"f1": v1, "f2": v2}}`.
        let mut innerSchemaEntries : Array (TSyntax `term) := #[]
        let mut innerFieldNames : Array (TSyntax `term) := #[]
        let mut fieldNameStrs : Array String := #[]
        let mut proofTerms : Array (TSyntax `term) := #[]
        for i in [:numArgs] do
          let param := xs[analysis.indVal.numParams + i]!
          let fieldName := (← param.fvarId!.getUserName).toString
          let fieldNameStx := Syntax.mkStrLit fieldName
          let argType ← inferType param
          let schemaTerm ← mkSchemaTermForType argType declName
          let proofTerm ← mkValidationProofTerm argType declName
          innerSchemaEntries := innerSchemaEntries.push (← `(term| ($fieldNameStx, $schemaTerm)))
          innerFieldNames := innerFieldNames.push fieldNameStx
          fieldNameStrs := fieldNameStrs.push fieldName
          proofTerms := proofTerms.push proofTerm
        let innerSchema ← `(term| objectSchema [$innerSchemaEntries,*] [$innerFieldNames,*])
        let schema ← `(term| objectSchema [($keyStx, $innerSchema)] [$keyStx])
        pure (schema, proofTerms, some (innerSchema, fieldNameStrs))
      else if numArgs == 1 then
        let argType ← inferType xs[analysis.indVal.numParams]!
        let schemaTerm ← mkSchemaTermForType argType declName
        let proofTerm ← mkValidationProofTerm argType declName
        let schema ← `(term| objectSchema [($keyStx, $schemaTerm)] [$keyStx])
        pure (schema, #[proofTerm], none)
      else
        let mut argSchemaTerms : Array (TSyntax `term) := #[]
        let mut proofTerms : Array (TSyntax `term) := #[]
        for i in [:numArgs] do
          let argType ← inferType xs[analysis.indVal.numParams + i]!
          argSchemaTerms := argSchemaTerms.push
            (← mkSchemaTermForType argType declName)
          proofTerms := proofTerms.push
            (← mkValidationProofTerm argType declName)
        let schema ←
          `(term| objectSchema [($keyStx, tupleSchema [$argSchemaTerms,*])] [$keyStx])
        pure (schema, proofTerms, none)
    schemaTerms := schemaTerms.push ctorSchema
    argCarryingSchemas := argCarryingSchemas.push ctorSchema
    argCarryingProofs := argCarryingProofs.push proofs
    argCarryingNamedInfo := argCarryingNamedInfo.push namedInfo

  let oneOfTerm ← if analysis.isRecursive then do
    let refNameStx := Syntax.mkStrLit declName.getString!
    `(term| oneOfSchema [$schemaTerms,*] (refName := some $refNameStx))
  else
    `(term| oneOfSchema [$schemaTerms,*])

  let mkOneOfExact (memProof innerProof : TSyntax `term) : CommandElabM (TSyntax `tactic) :=
    if analysis.isRecursive then do
      let refNameStx := Syntax.mkStrLit declName.getString!
      `(tactic| exact validateJson_oneOfSchema_correct _ _ _ $memProof $innerProof (some $refNameStx))
    else
      `(tactic| exact validateJson_oneOfSchema_correct _ _ _ $memProof $innerProof none)

  -- Build case-split tactics: `cases a` then one `case` tactic per constructor
  let mut caseTactics : Array (TSyntax `tactic) := #[]
  caseTactics := caseTactics.push (← `(tactic| cases a))
  let mut argCarryingIdx : Nat := 0
  let isPolymorphic := analysis.paramNames.size > 0

  for (ctorInfo, numArgs) in analysis.ctorInfos.zip analysis.argCounts do
    if numArgs == 0 then
      if isPolymorphic then
        -- Schema contains type params so native_decide can't close the whole goal.
        -- Target the string-enum branch (always at index 0) with a concrete sub-proof.
        let ctorShortName := ctorInfo.name.getString!
        let keyStx := Syntax.mkStrLit ctorShortName
        let exactTac ← mkOneOfExact (← `(term| List.Mem.head _)) (← `(term| (by native_decide)))
        caseTactics := caseTactics.push (← `(tactic| next =>
            show validateJson $oneOfTerm
              (Json.str $keyStx) = .ok ()
            $exactTac))
      else
        caseTactics := caseTactics.push (← `(tactic| next => native_decide))
    else
      let oneOfIdx := if analysis.hasZeroArgs then argCarryingIdx + 1 else argCarryingIdx

      let ctorShortName := ctorInfo.name.getString!
      let keyStx := Syntax.mkStrLit ctorShortName
      let memProof ← mkMemProof oneOfIdx

      -- All arg-carrying constructors use bridge theorems via mkObjBridgeHave.
      -- NOTE: The inner objectSchema proof must be bound via `have` so that Lean
      -- resolves all metavariables before the `by` tactic blocks run.
      let objSchema := argCarryingSchemas[argCarryingIdx]!
      let proofs := argCarryingProofs[argCarryingIdx]!
      let namedInfo := argCarryingNamedInfo[argCarryingIdx]!
      let oneOfExact ← mkOneOfExact memProof (← `(term| _inner))

      -- Build per-constructor proof. Named-arg constructors need a nested bridge
      -- (_namedObj for the inner objectSchema), while unnamed use the existing
      -- single-arg or tuple strategies.
      -- Uses literal idents in quotation so they share the macro scope with the
      -- `next` binder — `mkIdent` would create scope-free idents that don't match.
      let tac ← match namedInfo with
      | some (innerSchema, fieldNames) =>
        -- Named args: JSON encoding is {"ctor": {"f1": v1, "f2": v2, ...}}
        -- Proof: _namedObj proves inner objectSchema, _inner proves outer.
        let innerJsonValue ← match numArgs with
          | 1 => do
            let f0 := Syntax.mkStrLit fieldNames[0]!
            `(term| Json.mkObj [($f0, toJson _x)])
          | 2 => do
            let f0 := Syntax.mkStrLit fieldNames[0]!
            let f1 := Syntax.mkStrLit fieldNames[1]!
            `(term| Json.mkObj [($f0, toJson _x), ($f1, toJson _y)])
          | 3 => do
            let f0 := Syntax.mkStrLit fieldNames[0]!
            let f1 := Syntax.mkStrLit fieldNames[1]!
            let f2 := Syntax.mkStrLit fieldNames[2]!
            `(term| Json.mkObj [($f0, toJson _x), ($f1, toJson _y), ($f2, toJson _z)])
          | 4 => do
            let f0 := Syntax.mkStrLit fieldNames[0]!
            let f1 := Syntax.mkStrLit fieldNames[1]!
            let f2 := Syntax.mkStrLit fieldNames[2]!
            let f3 := Syntax.mkStrLit fieldNames[3]!
            `(term| Json.mkObj [($f0, toJson _x), ($f1, toJson _y),
                                ($f2, toJson _z), ($f3, toJson _w)])
          | _ => throwError "'deriving ValidatesAgainstSchema' unsupported: constructor \
              '{ctorShortName}' has {numArgs} named arguments (max 4)"
        let jsonValue ← `(term| Json.mkObj [($keyStx, $innerJsonValue)])
        let innerHValid ← mkNamedArgsInnerHValid numArgs proofs
        let namedObjHave ← mkNamedObjBridgeHave innerSchema innerJsonValue innerHValid
        let outerHValid ← mkNamedArgsOuterHValid
        let bridgeHave ← mkObjBridgeHave objSchema jsonValue outerHValid
        match numArgs with
        | 1 => `(tactic| next _x =>
            show validateJson $oneOfTerm ($jsonValue) = .ok ()
            $namedObjHave
            $bridgeHave
            $oneOfExact)
        | 2 => `(tactic| next _x _y =>
            show validateJson $oneOfTerm ($jsonValue) = .ok ()
            $namedObjHave
            $bridgeHave
            $oneOfExact)
        | 3 => `(tactic| next _x _y _z =>
            show validateJson $oneOfTerm ($jsonValue) = .ok ()
            $namedObjHave
            $bridgeHave
            $oneOfExact)
        | 4 => `(tactic| next _x _y _z _w =>
            show validateJson $oneOfTerm ($jsonValue) = .ok ()
            $namedObjHave
            $bridgeHave
            $oneOfExact)
        | _ => unreachable!
      | none =>
        -- Unnamed args: existing single-arg / tuple strategies
        let jsonValue ← match numArgs with
          | 1 => `(term| Json.mkObj [($keyStx, toJson _x)])
          | 2 => `(term| Json.mkObj [($keyStx, toJson (_x, _y))])
          | 3 => `(term| Json.mkObj [($keyStx, Json.arr #[toJson _x, toJson _y, toJson _z])])
          | 4 => `(term| Json.mkObj [($keyStx, Json.arr #[toJson _x, toJson _y, toJson _z, toJson _w])])
          | _ => throwError "'deriving ValidatesAgainstSchema' unsupported: constructor \
              '{ctorShortName}' has {numArgs} arguments (max 4)"
        let hValidBody ← if numArgs == 1 then do
          let argProof := proofs[0]!
          pure #[← `(tactic| intro name schema hns v hv),
                 ← `(tactic| simp only [List.mem_cons, Prod.mk.injEq,
                                         List.mem_nil_iff, or_false] at hns),
                 ← `(tactic| obtain ⟨rfl, rfl⟩ := hns),
                 -- simp_all handles non-recursive + direct recursive args.
                 -- Fall back to pre-computed proof for wrapped-recursive args
                 -- (e.g., Prod-wrapped recursion like `String × RecType`).
                 -- `done` ensures simp_all fully closes the goal; without it,
                 -- partial progress (e.g., substituting hv) tricks `first`
                 -- into skipping the fallback.
                 ← `(tactic| first
                    | (simp_all [ValidatesAgainstSchema.valid]; done)
                    | (simp_all only [List.mem_cons, Prod.mk.injEq,
                                      List.mem_nil_iff, or_false]
                       exact $argProof))]
        else
          mkTupleHValid numArgs proofs
        let bridgeHave ← mkObjBridgeHave objSchema jsonValue hValidBody
        -- Assemble: show + bridge have + oneOfExact, with per-arity binders.
        -- Literal idents in quotation share the ambient macro scope, ensuring the
        -- `next` binder and `jsonValue`/`mkTupleHValid` references resolve to the
        -- same variables. Programmatic `mkIdent` creates scope-free idents that
        -- would mismatch — hence the arity-specific patterns.
        match numArgs with
        | 1 => `(tactic| next _x =>
            show validateJson $oneOfTerm ($jsonValue) = .ok ()
            $bridgeHave
            $oneOfExact)
        | 2 => `(tactic| next _x _y =>
            show validateJson $oneOfTerm ($jsonValue) = .ok ()
            $bridgeHave
            $oneOfExact)
        | 3 => `(tactic| next _x _y _z =>
            show validateJson $oneOfTerm ($jsonValue) = .ok ()
            $bridgeHave
            $oneOfExact)
        | 4 => `(tactic| next _x _y _z _w =>
            show validateJson $oneOfTerm ($jsonValue) = .ok ()
            $bridgeHave
            $oneOfExact)
        | _ => unreachable!

      caseTactics := caseTactics.push tac
      argCarryingIdx := argCarryingIdx + 1

  let cmd ← `(command|
    instance : ValidatesAgainstSchema $(analysis.appliedType) where
      valid a := by $caseTactics*
  )
  elabCommand cmd
  closePolySection analysis.paramNames
  return true

def mkValidatesInstanceCmd (declName : Name) : CommandElabM Bool := do
  if ← mkEnumValidatesInstanceCmd declName then return true
  if ← mkStructValidatesInstanceCmd declName then return true
  if ← mkInductiveValidatesInstanceCmd declName then return true
  return false

def validatesAgainstSchemaHandler (declNames : Array Name) : CommandElabM Bool := do
  let mut succeeded := false
  for declName in declNames do
    if ← mkValidatesInstanceCmd declName then
      succeeded := true
    else
      logInfo m!"Could not derive ValidatesAgainstSchema for {declName}"
  unless succeeded do
    throwError "Could not derive ValidatesAgainstSchema for any of the types"
  return succeeded

end JsonSchema.Derive

initialize
  Lean.Elab.registerDerivingHandler ``JsonSchema.ValidatesAgainstSchema
    JsonSchema.Derive.validatesAgainstSchemaHandler
