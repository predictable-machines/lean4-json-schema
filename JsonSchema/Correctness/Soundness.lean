import PredictableJsonSchema.Schema
import PredictableJsonSchema.Validation

namespace JsonSchema

open Lean (Json JsonNumber)

-- Orphan DecidableEq for Except: Lean/Std don't provide one.
-- Scoped to prevent diamond conflicts if another package defines its own.
-- Remove if it's added upstream (check on Lean toolchain upgrades).
scoped instance [DecidableEq α] [DecidableEq β] : DecidableEq (Except α β)
  | .ok a, .ok b => if h : a = b then .isTrue (h ▸ rfl) else .isFalse (by intro h'; cases h'; exact h rfl)
  | .error a, .error b => if h : a = b then .isTrue (h ▸ rfl) else .isFalse (by intro h'; cases h'; exact h rfl)
  | .ok _, .error _ => .isFalse (by intro h; cases h)
  | .error _, .ok _ => .isFalse (by intro h; cases h)

/-- Json.null validates against nullSchema. -/
theorem validateJson_nullSchema : validateJson nullSchema .null = .ok () := by
  simp [validateJson, nullSchema]

/-- A string that belongs to a string-enum schema always validates successfully. -/
theorem validateJson_stringEnum_mem (vals : List String) (s : String) (h : s ∈ vals)
    : validateJson { kind := .string, enum := some vals } (.str s) = .ok () := by
  simp [validateJson, h]

/-- Any string validates against a plain stringSchema (no enum restriction). -/
theorem validateJson_stringSchema (s : String)
    : validateJson stringSchema (.str s) = .ok () := by
  simp [validateJson, stringSchema]

/-- Any boolean validates against booleanSchema. -/
theorem validateJson_booleanSchema (b : Bool)
    : validateJson booleanSchema (.bool b) = .ok () := by
  simp [validateJson, booleanSchema]

/-- Any number validates against an unbounded integerSchema. -/
theorem validateJson_integerSchema (n : JsonNumber)
    : validateJson integerSchema (.num n) = .ok () := by
  simp [validateJson, integerSchema, validateRange]

/-- Any number validates against an unbounded numberSchema. -/
theorem validateJson_numberSchema (n : JsonNumber)
    : validateJson numberSchema (.num n) = .ok () := by
  simp [validateJson, numberSchema, validateRange]

/-- A number within range validates against a bounded integerSchema.
    Decomposes integer validation into the range check alone. -/
theorem validateJson_integerSchema_range (n : JsonNumber)
    (lo hi : Option JsonNumber)
    (hRange : validateRange n lo hi = .ok ())
    : validateJson (integerSchema lo hi) (.num n) = .ok () := by
  simp [validateJson, integerSchema, hRange]

/-- A number within range validates against a bounded numberSchema. -/
theorem validateJson_numberSchema_range (n : JsonNumber)
    (lo hi : Option JsonNumber)
    (hRange : validateRange n lo hi = .ok ())
    : validateJson (numberSchema lo hi) (.num n) = .ok () := by
  simp [validateJson, numberSchema, hRange]

/-- Array schema validation decomposes into per-item validation:
    if every item validates against the item schema, the overall
    array validation succeeds. -/
theorem validateJson_arraySchema_correct (itemSchema : JSONSchema) (items : Array Json)
    (hItems : validateArrayItems itemSchema items.toList 0 = .ok ())
    : validateJson (arraySchema itemSchema) (.arr items) = .ok () := by
  simp [validateJson, arraySchema, hItems]

/-- Object schema validation decomposes into three independent checks:
    required fields present, no unknown fields, and per-property validation.
    When all three pass, the overall object validation succeeds. -/
theorem validateJson_objectSchema_correct
    (props : List (String × JSONSchema))
    (req : List String)
    (obj : Std.TreeMap.Raw String Json compare)
    (hReq : checkRequired req (.obj obj) = .ok ())
    (hUnk : checkUnknownFields obj.toList props = .ok ())
    (hProps : validateProps props obj.toList = .ok ())
    : validateJson (objectSchema props req) (.obj obj) = .ok () := by
  simp [validateJson, objectSchema, hReq, hUnk, hProps]

/-- If any schema in the list validates the JSON, validateOneOfSchemas succeeds. -/
private theorem validateOneOfSchemas_mem
    (schemas : List JSONSchema) (json : Json) (s : JSONSchema)
    (hMem : s ∈ schemas) (hOk : validateJson s json = .ok ())
    : validateOneOfSchemas schemas json = .ok () := by
  induction hMem with
  | head => simp [validateOneOfSchemas, hOk]
  | tail _ _ ih => simp only [validateOneOfSchemas]; split <;> simp_all

/-- oneOf validation ignores refName; threaded through for recursive oneOfSchema callers. -/
theorem validateJson_oneOfSchema_correct
    (schemas : List JSONSchema) (json : Json) (s : JSONSchema)
    (hMem : s ∈ schemas)
    (hOk : validateJson s json = .ok ())
    (refName : Option String)
    : validateJson { kind := .oneOf, oneOf := some schemas, refName := refName } json = .ok () := by
  unfold validateJson
  exact validateOneOfSchemas_mem schemas json s hMem hOk

/-- anySchema validates any JSON value regardless of refName (which is a
    serialization-only annotation ignored by validateJson). -/
@[simp] theorem validateJson_anySchema (refName : Option String) (json : Json)
    : validateJson (anySchema (refName := refName)) json = .ok () := by
  simp only [anySchema]; unfold validateJson; simp

/-- validatePrefixItems succeeds when each schema validates its corresponding value. -/
private theorem validatePrefixItems_all
    (schemas : List JSONSchema) (values : List Json)
    (hLen : schemas.length ≤ values.length)
    (hValid : ∀ i (hi : i < schemas.length),
      validateJson schemas[i] (values[i]'(by omega)) = .ok ())
    (idx : Nat)
    : validatePrefixItems schemas values idx = .ok () := by
  induction schemas generalizing values idx with
  | nil => simp [validatePrefixItems]
  | cons s ss ih =>
    cases values with
    | nil => simp at hLen
    | cons v vs =>
      have h0 : validateJson s v = .ok () := by
        have := hValid 0 (by simp)
        simpa using this
      simp only [validatePrefixItems, h0]
      exact ih vs (by simp at hLen; omega) (fun i hi => by
        have := hValid (i + 1) (by simp; omega)
        simpa using this) (idx + 1)

/-- General tuple validation: an n-element array validates against an n-schema tupleSchema
    when each schema-value pair validates individually. -/
theorem validateJson_tupleSchema
    (schemas : List JSONSchema) (values : List Json)
    (hLen : schemas.length ≤ values.length)
    (hValid : ∀ i (hi : i < schemas.length),
      validateJson schemas[i] (values[i]'(by omega)) = .ok ())
    : validateJson (tupleSchema schemas) (.arr ⟨values⟩) = .ok () := by
  have hPre := validatePrefixItems_all schemas values hLen hValid 0
  simp only [tupleSchema]; unfold validateJson; simp [hPre]

/-- A 2-element array validates against a 2-schema tupleSchema. -/
theorem validateJson_tupleSchema_pair
    (s1 s2 : JSONSchema) (v1 v2 : Json)
    (h1 : validateJson s1 v1 = .ok ())
    (h2 : validateJson s2 v2 = .ok ())
    : validateJson (tupleSchema [s1, s2]) (.arr #[v1, v2]) = .ok () := by
  simp only [tupleSchema]; unfold validateJson
  unfold validatePrefixItems; simp only [h1]
  unfold validatePrefixItems; simp only [h2]
  unfold validatePrefixItems; simp

/-- A 3-element array validates against a 3-schema tupleSchema. -/
theorem validateJson_tupleSchema_triple
    (s1 s2 s3 : JSONSchema) (v1 v2 v3 : Json)
    (h1 : validateJson s1 v1 = .ok ())
    (h2 : validateJson s2 v2 = .ok ())
    (h3 : validateJson s3 v3 = .ok ())
    : validateJson (tupleSchema [s1, s2, s3]) (.arr #[v1, v2, v3]) = .ok () := by
  simp only [tupleSchema]; unfold validateJson
  unfold validatePrefixItems; simp only [h1]
  unfold validatePrefixItems; simp only [h2]
  unfold validatePrefixItems; simp only [h3]
  unfold validatePrefixItems; simp

/-- A 4-element array validates against a 4-schema tupleSchema. -/
theorem validateJson_tupleSchema_quad
    (s1 s2 s3 s4 : JSONSchema) (v1 v2 v3 v4 : Json)
    (h1 : validateJson s1 v1 = .ok ())
    (h2 : validateJson s2 v2 = .ok ())
    (h3 : validateJson s3 v3 = .ok ())
    (h4 : validateJson s4 v4 = .ok ())
    : validateJson (tupleSchema [s1, s2, s3, s4]) (.arr #[v1, v2, v3, v4]) = .ok () := by
  simp only [tupleSchema]; unfold validateJson
  unfold validatePrefixItems; simp only [h1]
  unfold validatePrefixItems; simp only [h2]
  unfold validatePrefixItems; simp only [h3]
  unfold validatePrefixItems; simp only [h4]
  unfold validatePrefixItems; simp

/-- Any list of JSON values validates against anySchema item-by-item.
    This is the key lemma for proving wrapped-recursive types (e.g., `List RecT`)
    validate, since `anySchema` accepts anything. -/
@[simp] theorem validateArrayItems_anySchema (refName : Option String)
    (items : List Json) (idx : Nat)
    : validateArrayItems (anySchema (refName := refName)) items idx = .ok () := by
  induction items generalizing idx with
  | nil => simp [validateArrayItems]
  | cons _ _ ih =>
    simp only [validateArrayItems, validateJson_anySchema]
    exact ih (idx + 1)

end JsonSchema
