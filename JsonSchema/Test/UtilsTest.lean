import JsonSchema.Utils.Json

/-! Tests for JsonSchema.Utils -/

open JsonSchema.Utils
open Lean (Json)

-- ============================================================================
-- schemaIsTopLevelArray
-- ============================================================================

#guard schemaIsTopLevelArray (.mkObj [("type", "array"), ("items", .mkObj [("type", "string")])]) == true
#guard schemaIsTopLevelArray (.mkObj [("type", "object")]) == false
#guard schemaIsTopLevelArray (.mkObj [("type", "string")]) == false

-- ============================================================================
-- wrapArraySchema / unwrapArrayResult
-- ============================================================================

-- Wrapped schema is no longer a top-level array
#guard schemaIsTopLevelArray (wrapArraySchema (.mkObj [("type", "array")])) == false

-- Round-trip: wrap then unwrap preserves original data
private def testArrayResult : Json := .arr #[.str "a", .str "b"]
private def testWrapped : Json := .mkObj [("items", testArrayResult)]
#guard unwrapArrayResult testWrapped == testArrayResult

-- unwrapArrayResult on non-wrapped input returns input unchanged
#guard unwrapArrayResult (.str "hello") == .str "hello"
