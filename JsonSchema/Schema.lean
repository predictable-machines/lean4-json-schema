import Lean.Data.Json

namespace JsonSchema

open Lean (Json JsonNumber)

-- `SchemaKind` doubles as both a JSON Schema "type" value and a tag for composite
-- schema forms. `.oneOf` and `.any` don't correspond to JSON Schema types — they
-- signal that the schema's content lives in other fields (the `oneOf` list, or no
-- constraints at all). `toJsonString` returns "" for these, and `toLeanJsonCore`
-- skips the "type" entry entirely.
inductive SchemaKind where
  | string | integer | number | boolean | array | object | oneOf | null | any
  deriving Repr, BEq, DecidableEq

def SchemaKind.toJsonString : SchemaKind → String
  | .string  => "string"
  | .integer => "integer"
  | .number  => "number"
  | .boolean => "boolean"
  | .array   => "array"
  | .object  => "object"
  -- oneOf and any schemas omit the "type" field entirely; toLeanJsonCore skips
  -- the "type" entry for these kinds. The empty strings are never emitted.
  | .oneOf   => ""
  | .null    => "null"
  | .any     => ""

structure JSONSchema where
  kind : SchemaKind
  properties : Option (List (String × JSONSchema)) := none
  items : Option JSONSchema := none
  /-- JSON Schema prefixItems: positional item schemas for tuple-like arrays.
      Item at index i must validate against schema i. -/
  prefixItems : Option (List JSONSchema) := none
  required : List String := []
  description : Option String := none
  enum : Option (List String) := none
  minimum : Option JsonNumber := none
  maximum : Option JsonNumber := none
  /-- JSON Schema oneOf: valid when any one of the listed schemas matches.
      When set, the "type" field is omitted from the output (they're mutually exclusive). -/
  oneOf : Option (List JSONSchema) := none
  /-- When set, the internal serializer renders this as `{"$ref": "#/$defs/{refName}"}`.
      Used only for serialization of recursive positions; `validateJson` ignores this field. -/
  refName : Option String := none
  deriving Repr

namespace JSONSchema

theorem sizeOf_properties_lt (schema : JSONSchema)
    (props : List (String × JSONSchema))
    (h : schema.properties = some props) : sizeOf props < sizeOf schema := by
  cases schema with | mk => subst h; simp [JSONSchema.mk.sizeOf_spec]; omega

theorem sizeOf_items_lt (schema : JSONSchema) (itemSchema : JSONSchema)
    (h : schema.items = some itemSchema) : sizeOf itemSchema < sizeOf schema := by
  cases schema with | mk => subst h; simp [JSONSchema.mk.sizeOf_spec]; omega

theorem sizeOf_prefixItems_lt (schema : JSONSchema)
    (schemas : List JSONSchema)
    (h : schema.prefixItems = some schemas) : sizeOf schemas < sizeOf schema := by
  cases schema with | mk => subst h; simp [JSONSchema.mk.sizeOf_spec]; omega

theorem sizeOf_oneOf_lt (schema : JSONSchema) (schemas : List JSONSchema)
    (h : schema.oneOf = some schemas) : sizeOf schemas < sizeOf schema := by
  cases schema with | mk => subst h; simp [JSONSchema.mk.sizeOf_spec]; omega

mutual
  /-- Internal recursive serializer. Use `toLeanJson` for the public API. -/
  private def toLeanJsonCore (schema : JSONSchema) : Json :=
    match schema.refName with
    | some name => Json.mkObj [("$ref", Json.str s!"#/$defs/{name}")]
    | none =>
    let fields : List (String × Json) :=
      match schema.kind with
      | .oneOf | .any => []
      | k => [("type", Json.str k.toJsonString)]
    let fields := match schema.description with
      | some d => fields ++ [("description", Json.str d)]
      | none => fields
    let fields := match _hp : schema.properties with
      | some props =>
          let propsObj := Json.mkObj (toLeanJsonCoreProps props)
          fields ++ [("properties", propsObj), ("additionalProperties", Json.bool false)]
      | none => fields
    let fields := if schema.required.isEmpty then fields
      else fields ++ [("required", Json.arr (schema.required.map Json.str).toArray)]
    let fields := match _hi : schema.items with
      | some itemSchema => fields ++ [("items", toLeanJsonCore itemSchema)]
      | none => fields
    let fields := match _hpi : schema.prefixItems with
      | some schemas => fields ++ [("prefixItems", Json.arr (toLeanJsonCoreSchemas schemas).toArray)]
      | none => fields
    let fields := match schema.enum with
      | some vals => fields ++ [("enum", Json.arr (vals.map Json.str).toArray)]
      | none => fields
    let fields := match schema.minimum with
      | some m => fields ++ [("minimum", Json.num m)]
      | none => fields
    let fields := match schema.maximum with
      | some m => fields ++ [("maximum", Json.num m)]
      | none => fields
    let fields := match _ho : schema.oneOf with
      | some schemas => fields ++ [("oneOf", Json.arr (toLeanJsonCoreSchemas schemas).toArray)]
      | none => fields
    Json.mkObj fields
  termination_by sizeOf schema
  decreasing_by
    all_goals simp_wf
    all_goals first
      | omega
      | exact sizeOf_properties_lt _ _ _hp
      | exact sizeOf_items_lt _ _ _hi
      | exact sizeOf_prefixItems_lt _ _ _hpi
      | exact sizeOf_oneOf_lt _ _ _ho

  private def toLeanJsonCoreProps (props : List (String × JSONSchema)) : List (String × Json) :=
    match props with
    | [] => []
    | (name, s) :: rest => (name, toLeanJsonCore s) :: toLeanJsonCoreProps rest
  termination_by sizeOf props
  decreasing_by all_goals simp_wf; omega

  private def toLeanJsonCoreSchemas (schemas : List JSONSchema) : List Json :=
    match schemas with
    | [] => []
    | s :: rest => toLeanJsonCore s :: toLeanJsonCoreSchemas rest
  termination_by sizeOf schemas
  decreasing_by all_goals simp_wf; omega
end

end JSONSchema

class HasJSONSchema (α : Type) where
  toSchema : JSONSchema

namespace HasJSONSchema

instance : HasJSONSchema String where
  toSchema := { kind := .string }

instance : HasJSONSchema Nat where
  toSchema := { kind := .integer }

instance : HasJSONSchema Int where
  toSchema := { kind := .integer }

instance : HasJSONSchema Bool where
  toSchema := { kind := .boolean }

-- No ValidatesAgainstSchema instance for Float: Float.toJson can produce
-- Json.str for NaN/Infinity, which doesn't validate against numberSchema.
instance : HasJSONSchema Float where
  toSchema := { kind := .number }

instance [HasJSONSchema α] : HasJSONSchema (Array α) where
  toSchema := { kind := .array, items := some (toSchema (α := α)) }

instance [HasJSONSchema α] : HasJSONSchema (List α) where
  toSchema := { kind := .array, items := some (toSchema (α := α)) }

instance [HasJSONSchema α] : HasJSONSchema (Option α) where
  toSchema := { kind := .oneOf, oneOf := some [toSchema (α := α), { kind := .null }] }

end HasJSONSchema

def objectSchema (props : List (String × JSONSchema)) (req : List String := []) : JSONSchema :=
  { kind := .object, properties := some props, required := req }

def stringSchema (desc : Option String := none) (enum : Option (List String) := none) : JSONSchema :=
  { kind := .string, description := desc, enum := enum }

def integerSchema (min : Option JsonNumber := none) (max : Option JsonNumber := none) : JSONSchema :=
  { kind := .integer, minimum := min, maximum := max }

def numberSchema (min : Option JsonNumber := none) (max : Option JsonNumber := none) : JSONSchema :=
  { kind := .number, minimum := min, maximum := max }

def booleanSchema : JSONSchema :=
  { kind := .boolean }

-- Not @[simp]: derive handler proofs match on `arraySchema` structurally.
def arraySchema (itemSchema : JSONSchema) : JSONSchema :=
  { kind := .array, items := some itemSchema }

def nullSchema : JSONSchema :=
  { kind := .null }

/-- Schema for a value that must match exactly one of the given sub-schemas.
    Used to represent tagged unions (inductives with argument-carrying constructors).
    When `refName` is set, this schema serializes as `$ref` at reference sites and
    its definition is hoisted to `$defs` by `toLeanJson`. -/
def oneOfSchema (schemas : List JSONSchema) (refName : Option String := none) : JSONSchema :=
  { kind := .oneOf, oneOf := some schemas, refName := refName }

/-- Schema that validates any JSON value. When `refName` is set, serializes as
    `{"$ref": "#/$defs/{refName}"}` for recursive type references; otherwise as `{}`. -/
-- Not @[simp]: dedicated @[simp] lemmas (validateJson_anySchema, validateArrayItems_anySchema)
-- match on `anySchema` in their LHS — unfolding it would break the match.
def anySchema (refName : Option String := none) : JSONSchema :=
  { kind := .any, refName := refName }

/-- Schema for a positionally-typed array (JSON Schema `prefixItems`).
    Item at index i must validate against schema i. -/
-- Not @[simp]: derive handler proofs match on `tupleSchema` structurally.
def tupleSchema (schemas : List JSONSchema) : JSONSchema :=
  { kind := .array, prefixItems := some schemas }

-- Generic fold over the JSONSchema tree. Applies `f` at each node and concatenates
-- the results with those collected from all sub-schemas (properties, items,
-- prefixItems, oneOf). Both `collectRefDefs` and `collectAllRefNames` are thin
-- wrappers around this to avoid duplicating the traversal + termination proof.
mutual
  def foldSchema (f : JSONSchema → List α) (schema : JSONSchema) : List α :=
    let self := f schema
    let fromProps := match _hp : schema.properties with
      | some props => foldSchemaProps f props
      | none => []
    let fromItems := match _hi : schema.items with
      | some itemSchema => foldSchema f itemSchema
      | none => []
    let fromPrefixItems := match _hpi : schema.prefixItems with
      | some schemas => foldSchemaList f schemas
      | none => []
    let fromOneOf := match _ho : schema.oneOf with
      | some schemas => foldSchemaList f schemas
      | none => []
    self ++ fromProps ++ fromItems ++ fromPrefixItems ++ fromOneOf
  termination_by sizeOf schema
  decreasing_by
    all_goals simp_wf
    all_goals first
      | omega
      | exact JSONSchema.sizeOf_properties_lt _ _ _hp
      | exact JSONSchema.sizeOf_items_lt _ _ _hi
      | exact JSONSchema.sizeOf_prefixItems_lt _ _ _hpi
      | exact JSONSchema.sizeOf_oneOf_lt _ _ _ho

  def foldSchemaProps (f : JSONSchema → List α) (props : List (String × JSONSchema))
      : List α :=
    match props with
    | [] => []
    | (_, s) :: rest => foldSchema f s ++ foldSchemaProps f rest
  termination_by sizeOf props
  decreasing_by all_goals simp_wf; omega

  def foldSchemaList (f : JSONSchema → List α) (schemas : List JSONSchema)
      : List α :=
    match schemas with
    | [] => []
    | s :: rest => foldSchema f s ++ foldSchemaList f rest
  termination_by sizeOf schemas
  decreasing_by all_goals simp_wf; omega
end

-- Recursively collect all (refName, definitionSchema) pairs from a schema tree.
-- A "definition schema" has both refName set AND oneOf populated — these are
-- recursive types whose definitions need hoisting to $defs.
-- Reference-only markers (anySchema with refName but no oneOf) are not collected.
def collectRefDefs (schema : JSONSchema) : List (String × JSONSchema) :=
  foldSchema (fun s => match s.refName, s.oneOf with
    | some name, some _ => [(name, s)]
    | _, _ => []) schema

-- Collect ALL refName values from the schema tree (both definition sites and
-- reference-only markers). Used to verify that every $ref will resolve.
def collectAllRefNames (schema : JSONSchema) : List String :=
  foldSchema (fun s => match s.refName with
    | some name => [name]
    | none => []) schema

/-- Decidable check: every refName in the tree has a corresponding entry in
    collectRefDefs (i.e., a definition site with both refName and oneOf set).
    This guarantees that toLeanJson will produce a $defs entry for every $ref. -/
def JSONSchema.checkRefsResolved (schema : JSONSchema) : Bool :=
  let allRefs := collectAllRefNames schema
  let defKeys := (collectRefDefs schema).map Prod.fst
  -- Use `decide` so the proof bridge is clean: decide_eq_true_eq converts
  -- `decide P = true` to `P` directly, avoiding BEq/elem indirection.
  allRefs.all (fun name => decide (name ∈ defKeys))

/-- Deduplicate a list of `(String × α)` pairs by key, keeping the first occurrence.
    O(n²) but acceptable: only used on schema `$defs` which are typically < 20 entries. -/
private def dedupByKey (pairs : List (String × α)) : List (String × α) :=
  pairs.foldl (fun acc (k, v) =>
    if acc.any (fun (k', _) => k' == k) then acc else acc ++ [(k, v)]) []

/-- Serialize a schema to `Lean.Json`.
    Recursive type definitions anywhere in the tree are hoisted to a top-level
    `$defs` block, with inline occurrences replaced by `$ref` pointers. -/
def JSONSchema.toLeanJson (schema : JSONSchema) : Lean.Json :=
  let defs := dedupByKey (collectRefDefs schema)
  if defs.isEmpty then
    schema.toLeanJsonCore
  else
    let defsJson := Lean.Json.mkObj (defs.map fun (name, s) =>
      -- Clear refName before serializing the definition body so it emits
      -- the full structure instead of a self-referencing $ref
      (name, ({ s with refName := none } : JSONSchema).toLeanJsonCore))
    match schema.refName with
    | some name =>
      -- Top-level IS a recursive type → $defs + $ref (e.g., TypeExpr.toLeanJson)
      Lean.Json.mkObj [("$defs", defsJson),
                       ("$ref", Lean.Json.str s!"#/$defs/{name}")]
    | none =>
      -- Top-level is NOT recursive but CONTAINS recursive types (e.g., SpecSchema)
      -- Inject $defs into the serialized object
      let mainJson := schema.toLeanJsonCore
      match mainJson with
      | .obj kvs => Lean.Json.mkObj (("$defs", defsJson) :: kvs.toList)
      | other => Lean.Json.mkObj [("$defs", defsJson), ("allOf", .arr #[other])]

def JSONSchema.toJsonString (schema : JSONSchema) : String :=
  schema.toLeanJson.compress

end JsonSchema
