import Lean.Data.Json

/-!
# JSON Schema Utilities

Generic helpers for manipulating JSON Schema documents as `Lean.Json` values.
-/

namespace JsonSchema.Utils

open Lean (Json)

/-- Returns true when the top-level schema describes an array type. -/
def schemaIsTopLevelArray (schema : Json) : Bool :=
  (schema.getObjValAs? String "type" |>.toOption |>.getD "") == "array"

/-- Wraps a top-level array schema in an object with a single "items" property.
    Useful when a consumer requires an object schema at the top level.
    Use `unwrapArrayResult` to extract the inner value from the response. -/
def wrapArraySchema (schema : Json) : Json :=
  .mkObj [
    ("type", "object"),
    ("properties", .mkObj [("items", schema)]),
    ("required", .arr #[.str "items"])
  ]

/-- Extracts the "items" field from a response produced with a wrapped
    array schema (see `wrapArraySchema`). Returns the input unchanged
    if no "items" field is found. -/
def unwrapArrayResult (json : Json) : Json :=
  json.getObjVal? "items" |>.toOption |>.getD json

end JsonSchema.Utils
