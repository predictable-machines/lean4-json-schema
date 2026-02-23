import PredictableJsonSchema.Schema
import PredictableJsonSchema.Validation

namespace JsonSchema

open Lean (Json JsonNumber ToJson toJson)

/-! # Schema Validation Correctness

End-to-end correctness: for any type with both a derived `HasJSONSchema` and `Lean.ToJson`
instance, `validateJson schema (toJson a) = .ok ()` for every value `a`.
-/

class ValidatesAgainstSchema (α : Type) [HasJSONSchema α] [ToJson α] : Prop where
  valid : ∀ (a : α), validateJson (HasJSONSchema.toSchema (α := α)) (toJson a) = .ok ()

@[simp] theorem validates_against_schema [HasJSONSchema α] [ToJson α] [ValidatesAgainstSchema α]
    (a : α) : validateJson (HasJSONSchema.toSchema (α := α)) (toJson a) = .ok () :=
  ValidatesAgainstSchema.valid a

-- ============================================================================
-- Base type instances
-- ============================================================================

instance : ValidatesAgainstSchema String where
  valid s := by
    simp [HasJSONSchema.toSchema, toJson, validateJson]

instance : ValidatesAgainstSchema Bool where
  valid b := by
    simp [HasJSONSchema.toSchema, toJson, validateJson]

instance : ValidatesAgainstSchema Nat where
  valid n := by
    simp [HasJSONSchema.toSchema, toJson, validateJson, validateRange]

instance : ValidatesAgainstSchema Int where
  valid n := by
    simp [HasJSONSchema.toSchema, toJson, validateJson, validateRange]

-- Float is tricky: Float.toJson can produce either Json.num or Json.str (for NaN/Infinity).
-- We skip Float for now since the proof requires case-splitting on JsonNumber.fromFloat?.

-- ============================================================================
-- Collection instances
-- ============================================================================

/-- If every element validates, then validateArrayItems succeeds on the mapped list. -/
theorem validateArrayItems_of_forall
    (itemSchema : JSONSchema) (items : List α) [ToJson α]
    (h : ∀ a ∈ items, validateJson itemSchema (toJson a) = .ok ())
    (idx : Nat)
    : validateArrayItems itemSchema (items.map toJson) idx = .ok () := by
  induction items generalizing idx with
  | nil => simp [List.map, validateArrayItems]
  | cons x xs ih =>
    simp only [List.map]
    simp only [validateArrayItems]
    have hx := h x (List.Mem.head _)
    rw [hx]
    exact ih (fun a ha => h a (List.Mem.tail _ ha)) (idx + 1)

instance [HasJSONSchema α] [ToJson α] [ValidatesAgainstSchema α]
    : ValidatesAgainstSchema (Array α) where
  valid arr := by
    simp only [HasJSONSchema.toSchema, toJson, Array.toJson, validateJson]
    rw [Array.toList_map]
    exact validateArrayItems_of_forall _ arr.toList
      (fun a _ => ValidatesAgainstSchema.valid a) 0

instance [HasJSONSchema α] [ToJson α] [ValidatesAgainstSchema α]
    : ValidatesAgainstSchema (List α) where
  valid xs := by
    simp only [HasJSONSchema.toSchema, toJson, List.toJson, Array.toJson,
      validateJson]
    rw [Array.toList_map, List.toList_toArray]
    exact validateArrayItems_of_forall _ xs
      (fun a _ => ValidatesAgainstSchema.valid a) 0

/-- Option validates: some a validates via the first oneOf branch, none via nullSchema. -/
instance [HasJSONSchema α] [ToJson α] [ValidatesAgainstSchema α]
    : ValidatesAgainstSchema (Option α) where
  valid
    | some a => by
      simp only [HasJSONSchema.toSchema, toJson, Option.toJson]
      unfold validateJson validateOneOfSchemas
      simp only
      rw [ValidatesAgainstSchema.valid (α := α)]
    | none => by
      simp only [HasJSONSchema.toSchema, toJson, Option.toJson]
      unfold validateJson validateOneOfSchemas
      simp only
      -- The first oneOf branch (toSchema α on null) is abstract; split on its result
      split
      · rfl
      · unfold validateOneOfSchemas validateJson validateOneOfSchemas
        simp

end JsonSchema
