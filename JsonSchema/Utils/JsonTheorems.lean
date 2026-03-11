import JsonSchema.Utils.Json
import Std.Data.TreeMap.Raw.Lemmas
import Std.Data.TreeMap.Raw.WF

/-!
# JSON Schema Utility Theorems

Correctness theorems for the JSON helper functions in `JsonSchema.Utils`.
-/

namespace JsonSchema.Utils

open Lean (Json)

-- ---- Bridge lemmas ----
-- Json.mkObj builds a TreeMap.Raw internally, so proving anything about
-- getObjVal? requires reasoning through TreeMap insert/lookup. These private
-- lemmas isolate that plumbing so the public theorems stay clean.

-- Bridge lemma: singleton mkObj lookup always succeeds.
private theorem bridge_getObjVal_singleton (k : String) (v : Json) :
    (Json.mkObj [(k, v)]).getObjVal? k = .ok v := by
  simp only [Json.mkObj, Json.getObjVal?]
  have : (∅ : Std.TreeMap.Raw String Json compare).WF := Std.TreeMap.Raw.WF.empty
  simp [this, pure, Except.pure]

-- Bridge lemma: "type" lookup in a 3-key mkObj returns the first entry.
private theorem bridge_getObjVal_type (v props req : Json) :
    (Json.mkObj [("type", v), ("properties", props), ("required", req)]).getObjVal? "type"
      = .ok v := by
  simp only [Json.mkObj, Json.getObjVal?]
  rw [Std.TreeMap.Raw.ofList_cons]
  have hwf : ((∅ : Std.TreeMap.Raw String Json compare).insert "type" v).WF :=
    Std.TreeMap.Raw.WF.empty.insert
  simp only [Std.TreeMap.Raw.get?_eq_getElem?]
  rw [Std.TreeMap.Raw.getElem?_insertMany_list_of_contains_eq_false hwf
    (by simp only [List.map]; decide)]
  have hempty : (∅ : Std.TreeMap.Raw String Json compare).WF := Std.TreeMap.Raw.WF.empty
  simp [hempty, pure, Except.pure]

/-- Wrapping always produces a non-array top-level schema. -/
theorem wrapArraySchema_not_topLevelArray (schema : Json) :
    schemaIsTopLevelArray (wrapArraySchema schema) = false := by
  simp only [schemaIsTopLevelArray, wrapArraySchema, Json.getObjValAs?, Json.getObjValD,
        bridge_getObjVal_type]
  decide

/-- Unwrapping extracts the "items" field from an object that has one. -/
theorem unwrapArrayResult_mkObj_items (v : Json) :
    unwrapArrayResult (Json.mkObj [("items", v)]) = v := by
  simp only [unwrapArrayResult, bridge_getObjVal_singleton, Except.toOption, Option.getD]

end JsonSchema.Utils
