import PredictableJsonSchema.Schema
import PredictableJsonSchema.Validation

namespace JsonSchema

open Lean (Json JsonNumber)

-- ══════════════════════════════════════════════════════════════
-- Completeness: validation success implies structural constraints
-- ══════════════════════════════════════════════════════════════

/-- Completeness: null validation success implies the JSON is null. -/
theorem validateJson_null_complete (json : Json)
    (h : validateJson nullSchema json = .ok ())
    : json = .null := by
  cases json <;> simp_all [validateJson, nullSchema]

/-- Completeness: string validation success implies the JSON is a string. -/
theorem validateJson_string_complete (json : Json)
    (h : validateJson stringSchema json = .ok ())
    : ∃ s, json = .str s := by
  cases json with
  | str s => exact ⟨s, rfl⟩
  | _ => simp [validateJson, stringSchema] at h

/-- Completeness: string-enum validation success implies the JSON is
    a string whose value belongs to the enum list. -/
theorem validateJson_stringEnum_complete (vals : List String) (json : Json)
    (h : validateJson { kind := .string, enum := some vals } json = .ok ())
    : ∃ s, json = .str s ∧ s ∈ vals := by
  cases json with
  | str s =>
    simp [validateJson] at h
    exact ⟨s, rfl, h⟩
  | _ => simp [validateJson] at h

/-- Completeness: boolean validation success implies the JSON is a boolean. -/
theorem validateJson_boolean_complete (json : Json)
    (h : validateJson booleanSchema json = .ok ())
    : ∃ b, json = .bool b := by
  cases json with
  | bool b => exact ⟨b, rfl⟩
  | _ => simp [validateJson, booleanSchema] at h

/-- Completeness: integer validation success implies the JSON is a number
    and the number passes the range check. -/
theorem validateJson_integer_complete (json : Json) (lo hi : Option JsonNumber)
    (h : validateJson (integerSchema lo hi) json = .ok ())
    : ∃ n, json = .num n ∧ validateRange n lo hi = .ok () := by
  cases json with
  | num n =>
    simp [validateJson, integerSchema] at h
    exact ⟨n, rfl, h⟩
  | _ => simp [validateJson, integerSchema] at h

/-- Completeness: number validation success implies the JSON is a number
    and the number passes the range check. -/
theorem validateJson_number_complete (json : Json) (lo hi : Option JsonNumber)
    (h : validateJson (numberSchema lo hi) json = .ok ())
    : ∃ n, json = .num n ∧ validateRange n lo hi = .ok () := by
  cases json with
  | num n =>
    simp [validateJson, numberSchema] at h
    exact ⟨n, rfl, h⟩
  | _ => simp [validateJson, numberSchema] at h

/-- Completeness: array validation success implies the JSON is an array
    whose items all validate against the item schema. -/
theorem validateJson_array_complete (itemSchema : JSONSchema) (json : Json)
    (h : validateJson (arraySchema itemSchema) json = .ok ())
    : ∃ items : Array Json,
        json = .arr items ∧ validateArrayItems itemSchema items.toList 0 = .ok () := by
  cases json with
  | arr items =>
    simp [validateJson, arraySchema] at h
    exact ⟨items, rfl, h⟩
  | _ => simp [validateJson, arraySchema] at h

/-- Completeness: object validation success implies the JSON is an object. -/
theorem validateJson_object_complete
    (props : List (String × JSONSchema))
    (req : List String)
    (json : Json)
    (h : validateJson (objectSchema props req) json = .ok ())
    : ∃ obj, json = .obj obj := by
  cases json with
  | obj obj => exact ⟨obj, rfl⟩
  | _ => simp [validateJson, objectSchema] at h

/-- Completeness: oneOf validation success implies some sub-schema validates the JSON. -/
theorem validateOneOfSchemas_complete (schemas : List JSONSchema) (json : Json)
    (h : validateOneOfSchemas schemas json = .ok ())
    : ∃ s, s ∈ schemas ∧ validateJson s json = .ok () := by
  induction schemas with
  | nil => simp [validateOneOfSchemas] at h
  | cons s rest ih =>
    unfold validateOneOfSchemas at h
    by_cases hv : validateJson s json = .ok ()
    · exact ⟨s, .head .., hv⟩
    · have hRest : validateOneOfSchemas rest json = .ok () := by
        revert h; cases hm : validateJson s json with
        | ok => exact absurd hm hv
        | error => simp
      obtain ⟨s', hs', hv'⟩ := ih hRest
      exact ⟨s', .tail s hs', hv'⟩

/-- Completeness: 2-tuple validation success implies the JSON is an array
    whose first two elements validate against the respective schemas. -/
theorem validateJson_tupleSchema_pair_complete
    (s1 s2 : JSONSchema) (json : Json)
    (h : validateJson (tupleSchema [s1, s2]) json = .ok ())
    : ∃ items : Array Json,
        json = .arr items ∧ validatePrefixItems [s1, s2] items.toList 0 = .ok () := by
  cases json with
  | arr items =>
    simp [validateJson, tupleSchema] at h
    -- simp leaves a match on the validatePrefixItems result
    cases hp : validatePrefixItems [s1, s2] items.toList 0 with
    | ok => exact ⟨items, rfl, hp⟩
    | error e => simp [hp] at h
  | _ => simp [validateJson, tupleSchema] at h

/-- Completeness: oneOf validation on a full schema succeeds iff some sub-schema validates. -/
theorem validateJson_oneOf_complete
    (schemas : List JSONSchema) (refName : Option String) (json : Json)
    (h : validateJson { kind := .oneOf, oneOf := some schemas, refName := refName } json = .ok ())
    : ∃ s, s ∈ schemas ∧ validateJson s json = .ok () := by
  unfold validateJson at h
  exact validateOneOfSchemas_complete schemas json h

end JsonSchema
