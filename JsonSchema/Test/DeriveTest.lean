import PredictableJsonSchema.Derive.SchemaValid

namespace JsonSchema.DeriveSchemaValid.Test

open Lean (Json ToJson toJson)
open JsonSchema

-- ============================================================================
-- Enums
-- ============================================================================

private inductive TestColor where
  | red | green | blue
  deriving HasJSONSchema, ToJson, ValidatesAgainstSchema

-- ============================================================================
-- Structures
-- ============================================================================

private structure TestSingle where
  val : String
  deriving HasJSONSchema, ToJson, ValidatesAgainstSchema

private structure TestPerson where
  name : String
  age : Nat
  deriving HasJSONSchema, ToJson, ValidatesAgainstSchema

private structure TestTriple where
  x : String
  y : Nat
  z : Bool
  deriving HasJSONSchema, ToJson, ValidatesAgainstSchema

private structure TestNested where
  person : TestPerson
  label : String
  deriving HasJSONSchema, ToJson, ValidatesAgainstSchema

private structure TestWithCollections where
  tags : Array String
  scores : List Nat
  nickname : Option String
  deriving HasJSONSchema, ToJson, ValidatesAgainstSchema

-- ============================================================================
-- Inductive types (non-enum, non-structure)
-- ============================================================================

-- Single-arg constructors only (all carry one payload)
private inductive TestValue where
  | text : String → TestValue
  | number : Nat → TestValue
  | flag : Bool → TestValue
  deriving HasJSONSchema, ToJson, ValidatesAgainstSchema

-- Mixed: zero-arg + single-arg constructors
private inductive TestMaybe where
  | nothing
  | just : String → TestMaybe
  deriving HasJSONSchema, ToJson, ValidatesAgainstSchema

-- Mixed with nested type payload
private inductive TestContainer where
  | empty
  | single : TestPerson → TestContainer
  | labeled : String → TestContainer
  deriving HasJSONSchema, ToJson, ValidatesAgainstSchema

-- Multi-arg constructor (falls back to descriptionOnly)
private inductive TestPair where
  | pair : String → Nat → TestPair
  deriving HasJSONSchema, ToJson, ValidatesAgainstSchema

-- Mixed: zero-arg, single-arg, and multi-arg constructors
private inductive TestShape where
  | point
  | circle : Nat → TestShape
  | rect : Nat → Nat → TestShape
  deriving HasJSONSchema, ToJson, ValidatesAgainstSchema

-- ============================================================================
-- Edge-case enums
-- ============================================================================

-- Single-variant enum (unit-like type)
private inductive TestUnit where
  | unit
  deriving HasJSONSchema, ToJson, ValidatesAgainstSchema

-- Large enum (7 variants)
private inductive TestDay where
  | monday | tuesday | wednesday | thursday | friday | saturday | sunday
  deriving HasJSONSchema, ToJson, ValidatesAgainstSchema

-- ============================================================================
-- Recursive inductive types
-- ============================================================================

-- Unary recursion: zero-arg base + single-arg recursive
private inductive TestPeano where
  | zero
  | succ : TestPeano → TestPeano
  deriving HasJSONSchema, ToJson, ValidatesAgainstSchema

-- Linked list: zero-arg base + 2-arg (non-recursive + recursive)
private inductive TestNatList where
  | nil
  | cons : Nat → TestNatList → TestNatList
  deriving HasJSONSchema, ToJson, ValidatesAgainstSchema

-- Binary tree: 1-arg non-recursive leaf + 2-arg recursive node
private inductive TestIntTree where
  | leaf : Int → TestIntTree
  | node : TestIntTree → TestIntTree → TestIntTree
  deriving HasJSONSchema, ToJson, ValidatesAgainstSchema

-- AST: 0-arg + 1-arg non-recursive + 1-arg recursive + 2-arg recursive
private inductive TestExpr where
  | zero
  | lit : Nat → TestExpr
  | neg : TestExpr → TestExpr
  | add : TestExpr → TestExpr → TestExpr
  deriving HasJSONSchema, ToJson, ValidatesAgainstSchema

-- All constructors carry args: 1-arg non-recursive + 2-arg recursive
private inductive TestStrTree where
  | text : String → TestStrTree
  | branch : TestStrTree → TestStrTree → TestStrTree
  deriving HasJSONSchema, ToJson, ValidatesAgainstSchema

-- 3-arg recursive constructor
private inductive TestTernaryTree where
  | leaf : String → TestTernaryTree
  | node : TestTernaryTree → TestTernaryTree → TestTernaryTree → TestTernaryTree
  deriving HasJSONSchema, ToJson, ValidatesAgainstSchema

-- 4-arg constructor (maximum supported arity)
private inductive TestQuadNode where
  | leaf
  | quad : TestQuadNode → TestQuadNode → TestQuadNode → TestQuadNode → TestQuadNode
  deriving HasJSONSchema, ToJson, ValidatesAgainstSchema

-- Recursive with structure payload: non-recursive struct arg + recursive self
private inductive TestLabeledTree where
  | leaf : TestPerson → TestLabeledTree
  | node : TestLabeledTree → TestLabeledTree → TestLabeledTree
  deriving HasJSONSchema, ToJson, ValidatesAgainstSchema

-- List-wrapped recursive: constructor arg is List of self
-- ValidatesAgainstSchema NOT derived here: Lean's `deriving ToJson` produces a `partial` def
-- for types with List/Prod-wrapped recursion, which is kernel-opaque and prevents proof automation.
-- See TestChildrenV2 below for the manual non-partial ToJson approach.
private inductive TestChildren where
  | leaf : String → TestChildren
  | node : List TestChildren → TestChildren
  deriving HasJSONSchema, ToJson

-- Prod-wrapped recursive: constructor arg is (String × self)
private inductive TestTaggedR where
  | empty
  | tagged : String × TestTaggedR → TestTaggedR
  deriving HasJSONSchema, ToJson

-- List of Prod-wrapped recursive: constructor arg is List (String × self)
private inductive TestNamedBranch where
  | leaf : Nat → TestNamedBranch
  | branches : List (String × TestNamedBranch) → TestNamedBranch
  deriving HasJSONSchema, ToJson

-- ============================================================================
-- Deeply nested structures
-- ============================================================================

private structure TestInnermost where
  value : Nat
  deriving HasJSONSchema, ToJson, ValidatesAgainstSchema

private structure TestMiddle where
  inner : TestInnermost
  tag : String
  deriving HasJSONSchema, ToJson, ValidatesAgainstSchema

private structure TestOutermost where
  middle : TestMiddle
  flag : Bool
  deriving HasJSONSchema, ToJson, ValidatesAgainstSchema

private structure TestFourLevels where
  outer : TestOutermost
  label : String
  deriving HasJSONSchema, ToJson, ValidatesAgainstSchema

-- ============================================================================
-- Complex field types (polymorphic composition via built-in instances)
-- ============================================================================

-- All fields optional
private structure TestAllOptional where
  name : Option String
  age : Option Nat
  active : Option Bool
  deriving HasJSONSchema, ToJson, ValidatesAgainstSchema

-- Nested Option
private structure TestNestedOption where
  value : Option (Option String)
  deriving HasJSONSchema, ToJson, ValidatesAgainstSchema

-- Array of Options
private structure TestArrayOfOptions where
  items : Array (Option Nat)
  deriving HasJSONSchema, ToJson, ValidatesAgainstSchema

-- Nested collections: List of Arrays, Array of Lists
private structure TestNestedCollections where
  matrix : List (Array String)
  rows : Array (List Nat)
  deriving HasJSONSchema, ToJson, ValidatesAgainstSchema

-- Option of collection
private structure TestOptionArray where
  data : Option (Array String)
  deriving HasJSONSchema, ToJson, ValidatesAgainstSchema

-- Array of nested arrays
private structure TestNestedArrays where
  grid : Array (Array Nat)
  deriving HasJSONSchema, ToJson, ValidatesAgainstSchema

-- Array of structures
private structure TestArrayOfStructs where
  people : Array TestPerson
  deriving HasJSONSchema, ToJson, ValidatesAgainstSchema

-- List of inductives
private structure TestListOfInductives where
  values : List TestValue
  deriving HasJSONSchema, ToJson, ValidatesAgainstSchema

-- Structure with Int field (tests Int instance)
private structure TestWithInt where
  offset : Int
  count : Nat
  deriving HasJSONSchema, ToJson, ValidatesAgainstSchema

-- ============================================================================
-- Structures containing inductive types
-- ============================================================================

-- Structure with enum fields
private structure TestWithEnums where
  day : TestDay
  color : TestColor
  deriving HasJSONSchema, ToJson, ValidatesAgainstSchema

-- Structure with oneOf inductive field
private structure TestWithInductive where
  value : TestValue
  label : String
  deriving HasJSONSchema, ToJson, ValidatesAgainstSchema

-- Structure with recursive inductive field
private structure TestWithRecursive where
  tree : TestIntTree
  name : String
  deriving HasJSONSchema, ToJson, ValidatesAgainstSchema

-- Structure with optional inductive field
private structure TestOptionalInductive where
  shape : Option TestShape
  active : Bool
  deriving HasJSONSchema, ToJson, ValidatesAgainstSchema

-- Structure with array of enums
private structure TestArrayOfEnums where
  colors : Array TestColor
  deriving HasJSONSchema, ToJson, ValidatesAgainstSchema

-- ============================================================================
-- Inductives with structure payloads
-- ============================================================================

-- Zero-arg + structure payload + string payload
private inductive TestResponse where
  | empty
  | data : TestPerson → TestResponse
  | error : String → TestResponse
  deriving HasJSONSchema, ToJson, ValidatesAgainstSchema

-- Inductive with nested structure payload
private inductive TestNestedPayload where
  | none
  | wrapped : TestNested → TestNestedPayload
  deriving HasJSONSchema, ToJson, ValidatesAgainstSchema

-- ============================================================================
-- Single-constructor inductives (not structures)
-- ============================================================================

-- Single constructor, 1 arg
private inductive TestWrapper where
  | wrap : String → TestWrapper
  deriving HasJSONSchema, ToJson, ValidatesAgainstSchema

-- Single constructor, 2 args
private inductive TestPairInductive where
  | make : String → Nat → TestPairInductive
  deriving HasJSONSchema, ToJson, ValidatesAgainstSchema

-- Single constructor, 3 args
private inductive TestTripleInductive where
  | make : String → Nat → Bool → TestTripleInductive
  deriving HasJSONSchema, ToJson, ValidatesAgainstSchema

-- Single constructor, 4 args
private inductive TestQuadInductive where
  | make : String → Nat → Bool → Int → TestQuadInductive
  deriving HasJSONSchema, ToJson, ValidatesAgainstSchema

-- ============================================================================
-- Polymorphic types (user-defined)
-- ============================================================================

-- Polymorphic structure: single type parameter
private structure TestBox (α : Type) where
  val : α
  deriving HasJSONSchema, ToJson, ValidatesAgainstSchema

-- Polymorphic structure: two type parameters
private structure TestEither (α β : Type) where
  left : α
  right : β
  deriving HasJSONSchema, ToJson, ValidatesAgainstSchema

-- Polymorphic structure with collection of type parameter
private structure TestTagged (α : Type) where
  tag : String
  values : Array α
  deriving HasJSONSchema, ToJson, ValidatesAgainstSchema

-- Polymorphic inductive: enum-like with payloads
private inductive TestResult (α β : Type) where
  | ok : α → TestResult α β
  | err : β → TestResult α β
  deriving HasJSONSchema, ToJson, ValidatesAgainstSchema

-- Polymorphic inductive: zero-arg + single-arg
private inductive TestMaybeOf (α : Type) where
  | nothing
  | just : α → TestMaybeOf α
  deriving HasJSONSchema, ToJson, ValidatesAgainstSchema

-- Polymorphic recursive: linked list
private inductive TestListOf (α : Type) where
  | nil
  | cons : α → TestListOf α → TestListOf α
  deriving HasJSONSchema, ToJson, ValidatesAgainstSchema

-- Polymorphic recursive: binary tree with data at leaves
private inductive TestTreeOf (α : Type) where
  | leaf : α → TestTreeOf α
  | node : TestTreeOf α → TestTreeOf α → TestTreeOf α
  deriving HasJSONSchema, ToJson, ValidatesAgainstSchema

-- Polymorphic with nested polymorphic fields
private structure TestComplex (α : Type) where
  main : α
  backup : Option α
  history : List α
  deriving HasJSONSchema, ToJson, ValidatesAgainstSchema

-- ============================================================================
-- Verify ALL instances exist (silent — no build output)
-- ============================================================================

-- Original tests
example : ValidatesAgainstSchema TestColor := inferInstance
example : ValidatesAgainstSchema TestSingle := inferInstance
example : ValidatesAgainstSchema TestPerson := inferInstance
example : ValidatesAgainstSchema TestTriple := inferInstance
example : ValidatesAgainstSchema TestNested := inferInstance
example : ValidatesAgainstSchema TestWithCollections := inferInstance
example : ValidatesAgainstSchema TestValue := inferInstance
example : ValidatesAgainstSchema TestMaybe := inferInstance
example : ValidatesAgainstSchema TestContainer := inferInstance
example : ValidatesAgainstSchema TestPair := inferInstance
example : ValidatesAgainstSchema TestShape := inferInstance

-- Edge-case enums
example : ValidatesAgainstSchema TestUnit := inferInstance
example : ValidatesAgainstSchema TestDay := inferInstance

-- Recursive types (directly recursive: handler-derived)
example : ValidatesAgainstSchema TestPeano := inferInstance
example : ValidatesAgainstSchema TestNatList := inferInstance
example : ValidatesAgainstSchema TestIntTree := inferInstance
example : ValidatesAgainstSchema TestExpr := inferInstance
example : ValidatesAgainstSchema TestStrTree := inferInstance
example : ValidatesAgainstSchema TestTernaryTree := inferInstance
example : ValidatesAgainstSchema TestQuadNode := inferInstance
example : ValidatesAgainstSchema TestLabeledTree := inferInstance

-- Deeply nested structures
example : ValidatesAgainstSchema TestInnermost := inferInstance
example : ValidatesAgainstSchema TestMiddle := inferInstance
example : ValidatesAgainstSchema TestOutermost := inferInstance
example : ValidatesAgainstSchema TestFourLevels := inferInstance

-- Complex field types
example : ValidatesAgainstSchema TestAllOptional := inferInstance
example : ValidatesAgainstSchema TestNestedOption := inferInstance
example : ValidatesAgainstSchema TestArrayOfOptions := inferInstance
example : ValidatesAgainstSchema TestNestedCollections := inferInstance
example : ValidatesAgainstSchema TestOptionArray := inferInstance
example : ValidatesAgainstSchema TestNestedArrays := inferInstance
example : ValidatesAgainstSchema TestArrayOfStructs := inferInstance
example : ValidatesAgainstSchema TestListOfInductives := inferInstance
example : ValidatesAgainstSchema TestWithInt := inferInstance

-- Cross-type composition
example : ValidatesAgainstSchema TestWithEnums := inferInstance
example : ValidatesAgainstSchema TestWithInductive := inferInstance
example : ValidatesAgainstSchema TestWithRecursive := inferInstance
example : ValidatesAgainstSchema TestOptionalInductive := inferInstance
example : ValidatesAgainstSchema TestArrayOfEnums := inferInstance
example : ValidatesAgainstSchema TestResponse := inferInstance
example : ValidatesAgainstSchema TestNestedPayload := inferInstance

-- Single-constructor inductives
example : ValidatesAgainstSchema TestWrapper := inferInstance
example : ValidatesAgainstSchema TestPairInductive := inferInstance
example : ValidatesAgainstSchema TestTripleInductive := inferInstance
example : ValidatesAgainstSchema TestQuadInductive := inferInstance

-- Polymorphic types (concrete instantiations)
example : ValidatesAgainstSchema (TestBox String) := inferInstance
example : ValidatesAgainstSchema (TestBox Nat) := inferInstance
example : ValidatesAgainstSchema (TestEither String Nat) := inferInstance
example : ValidatesAgainstSchema (TestTagged Bool) := inferInstance
example : ValidatesAgainstSchema (TestResult String Nat) := inferInstance
example : ValidatesAgainstSchema (TestMaybeOf String) := inferInstance
example : ValidatesAgainstSchema (TestMaybeOf (Array Nat)) := inferInstance
example : ValidatesAgainstSchema (TestListOf String) := inferInstance
example : ValidatesAgainstSchema (TestTreeOf Nat) := inferInstance
example : ValidatesAgainstSchema (TestComplex String) := inferInstance

-- ============================================================================
-- Wrapped-recursive manual proofs
-- ============================================================================

-- Test: non-partial ToJson enables ValidatesAgainstSchema for wrapped-recursive types.
-- Lean's `deriving ToJson` produces `partial` defs for recursive types with List/Prod-wrapped
-- constructors, making them kernel-opaque. Manual instances with structural recursion are needed.
private inductive TestChildrenV2 where
  | leaf : String → TestChildrenV2
  | node : List TestChildrenV2 → TestChildrenV2

-- Non-partial ToJson using explicit list recursion (structural recursion on the inductive)
mutual
  private def TestChildrenV2.toJsonImpl : TestChildrenV2 → Lean.Json
    | .leaf s => Lean.Json.mkObj [("leaf", Lean.toJson s)]
    | .node xs => Lean.Json.mkObj [("node", Lean.Json.arr (TestChildrenV2.listToJson xs).toArray)]
  private def TestChildrenV2.listToJson : List TestChildrenV2 → List Lean.Json
    | [] => []
    | x :: xs => TestChildrenV2.toJsonImpl x :: TestChildrenV2.listToJson xs
end

instance : Lean.ToJson TestChildrenV2 where toJson := TestChildrenV2.toJsonImpl
deriving instance HasJSONSchema for TestChildrenV2

-- Manual proof: simp normalizes both HasJSONSchema.toSchema and toJson, then bridge theorems close it.
-- This works because TestChildrenV2.toJsonImpl is non-partial (structural recursion via mutual block).
instance : ValidatesAgainstSchema TestChildrenV2 where
  valid a := by
    cases a with
    | leaf _x =>
      simp only [HasJSONSchema.toSchema, toJson, Lean.ToJson.toJson, TestChildrenV2.toJsonImpl]
      have inner : validateJson
          (objectSchema [("leaf", stringSchema)] ["leaf"])
          (Json.mkObj [("leaf", Json.str _x)]) = .ok () :=
        validateJson_mkObj_objectSchema
          [("leaf", stringSchema)] ["leaf"] [("leaf", Json.str _x)]
          (by simp only [List.map]; decide)
          (hReq_of_map_fst _ _ rfl)
          (by intro k hk; simp only [List.map] at hk ⊢; exact hk)
          (by intro name schema hns v hv
              simp only [List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at hns hv
              obtain ⟨rfl, rfl⟩ := hns; obtain ⟨-, rfl⟩ := hv
              simp [validateJson, stringSchema])
      exact validateJson_oneOfSchema_correct _ _ _ (List.Mem.head _) inner (some "TestChildrenV2")
    | node _x =>
      simp only [HasJSONSchema.toSchema, toJson, Lean.ToJson.toJson, TestChildrenV2.toJsonImpl]
      have inner : validateJson
          (objectSchema [("node", arraySchema (anySchema (refName := some "TestChildrenV2")))] ["node"])
          (Json.mkObj [("node", Json.arr (TestChildrenV2.listToJson _x).toArray)]) = .ok () :=
        validateJson_mkObj_objectSchema
          [("node", arraySchema (anySchema (refName := some "TestChildrenV2")))] ["node"]
          [("node", Json.arr (TestChildrenV2.listToJson _x).toArray)]
          (by simp only [List.map]; decide)
          (hReq_of_map_fst _ _ rfl)
          (by intro k hk; simp only [List.map] at hk ⊢; exact hk)
          (by intro name schema hns v hv
              simp only [List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at hns hv
              obtain ⟨rfl, rfl⟩ := hns; obtain ⟨-, rfl⟩ := hv
              simp [validateJson, arraySchema])
      exact validateJson_oneOfSchema_correct _ _ _
        (List.Mem.tail _ (List.Mem.head _)) inner (some "TestChildrenV2")

-- Wrapped-recursive types (manual non-partial ToJson + manual proof)
example : ValidatesAgainstSchema TestChildrenV2 := inferInstance

-- Prod-wrapped recursive: structural recursion works directly (no mutual block needed).
-- `toJsonImpl p.2` is a strict sub-term of `.tagged p`, so Lean accepts this as non-partial.
private inductive TestTaggedRV2 where
  | empty
  | tagged : String × TestTaggedRV2 → TestTaggedRV2

private def TestTaggedRV2.toJsonImpl : TestTaggedRV2 → Lean.Json
  | .empty => Lean.Json.str "empty"
  | .tagged p => Lean.Json.mkObj [("tagged", Lean.Json.arr #[Lean.toJson p.1, TestTaggedRV2.toJsonImpl p.2])]

instance : Lean.ToJson TestTaggedRV2 where toJson := TestTaggedRV2.toJsonImpl
deriving instance HasJSONSchema for TestTaggedRV2
deriving instance ValidatesAgainstSchema for TestTaggedRV2

example : ValidatesAgainstSchema TestTaggedRV2 := inferInstance

-- ============================================================================
-- $defs/$ref wrapping for recursive schemas
-- ============================================================================

-- Recursive Peano: $defs wraps the oneOf, top-level is $ref
private def expectedPeanoJson :=
  "{\"$defs\":{\"TestPeano\":{\"oneOf\":[" ++
    "{\"enum\":[\"zero\"],\"type\":\"string\"}," ++
    "{\"additionalProperties\":false," ++
      "\"properties\":{\"succ\":{\"$ref\":\"#/$defs/TestPeano\"}}," ++
      "\"required\":[\"succ\"]," ++
      "\"type\":\"object\"}" ++
  "]}}," ++
  "\"$ref\":\"#/$defs/TestPeano\"}"

-- Polymorphic recursive tree instantiated at Nat: leaf carries integer, node has two $refs
private def expectedTreeOfNatJson :=
  "{\"$defs\":{\"TestTreeOf\":{\"oneOf\":[" ++
    "{\"additionalProperties\":false," ++
      "\"properties\":{\"leaf\":{\"type\":\"integer\"}}," ++
      "\"required\":[\"leaf\"]," ++
      "\"type\":\"object\"}," ++
    "{\"additionalProperties\":false," ++
      "\"properties\":{\"node\":{" ++
        "\"prefixItems\":[{\"$ref\":\"#/$defs/TestTreeOf\"},{\"$ref\":\"#/$defs/TestTreeOf\"}]," ++
        "\"type\":\"array\"}}," ++
      "\"required\":[\"node\"]," ++
      "\"type\":\"object\"}" ++
  "]}}," ++
  "\"$ref\":\"#/$defs/TestTreeOf\"}"

-- Composite: non-recursive struct containing a recursive field; $defs hoisted to top
private def expectedWithRecursiveJson :=
  "{\"$defs\":{\"TestIntTree\":{\"oneOf\":[" ++
    "{\"additionalProperties\":false," ++
      "\"properties\":{\"leaf\":{\"type\":\"integer\"}}," ++
      "\"required\":[\"leaf\"]," ++
      "\"type\":\"object\"}," ++
    "{\"additionalProperties\":false," ++
      "\"properties\":{\"node\":{" ++
        "\"prefixItems\":[{\"$ref\":\"#/$defs/TestIntTree\"},{\"$ref\":\"#/$defs/TestIntTree\"}]," ++
        "\"type\":\"array\"}}," ++
      "\"required\":[\"node\"]," ++
      "\"type\":\"object\"}" ++
  "]}}," ++
  "\"additionalProperties\":false," ++
  "\"properties\":{" ++
    "\"name\":{\"type\":\"string\"}," ++
    "\"tree\":{\"$ref\":\"#/$defs/TestIntTree\"}}," ++
  "\"required\":[\"tree\",\"name\"]," ++
  "\"type\":\"object\"}"

private def expectedPersonJson :=
  "{\"additionalProperties\":false,\"properties\":{\"age\":{\"type\":\"integer\"},\"name\":{\"type\":\"string\"}},\"required\":[\"name\",\"age\"],\"type\":\"object\"}"

private def expectedColorJson :=
  "{\"enum\":[\"red\",\"green\",\"blue\"],\"type\":\"string\"}"

-- Recursive schemas include $defs/$ref wrapping
#guard (HasJSONSchema.toSchema (α := TestPeano)).toJsonString == expectedPeanoJson
#guard (HasJSONSchema.toSchema (α := TestTreeOf Nat)).toJsonString == expectedTreeOfNatJson

-- Composite types containing recursive inductives get $defs hoisted to the top level
#guard (HasJSONSchema.toSchema (α := TestWithRecursive)).toJsonString == expectedWithRecursiveJson

-- Non-recursive schemas have no $defs wrapping
#guard (HasJSONSchema.toSchema (α := TestPerson)).toJsonString == expectedPersonJson
#guard (HasJSONSchema.toSchema (α := TestColor)).toJsonString == expectedColorJson

-- ============================================================================
-- checkRefsResolved: every $ref has a corresponding definition
-- ============================================================================

-- Recursive types: all refNames resolve to definition sites
#guard (HasJSONSchema.toSchema (α := TestPeano)).checkRefsResolved
#guard (HasJSONSchema.toSchema (α := TestNatList)).checkRefsResolved
#guard (HasJSONSchema.toSchema (α := TestIntTree)).checkRefsResolved
#guard (HasJSONSchema.toSchema (α := TestExpr)).checkRefsResolved
#guard (HasJSONSchema.toSchema (α := TestStrTree)).checkRefsResolved
#guard (HasJSONSchema.toSchema (α := TestTernaryTree)).checkRefsResolved
#guard (HasJSONSchema.toSchema (α := TestQuadNode)).checkRefsResolved
#guard (HasJSONSchema.toSchema (α := TestLabeledTree)).checkRefsResolved
#guard (HasJSONSchema.toSchema (α := TestListOf String)).checkRefsResolved
#guard (HasJSONSchema.toSchema (α := TestTreeOf Nat)).checkRefsResolved

-- Wrapped-recursive types: List/Prod wrappers around recursive refs
#guard (HasJSONSchema.toSchema (α := TestChildren)).checkRefsResolved
#guard (HasJSONSchema.toSchema (α := TestTaggedR)).checkRefsResolved
#guard (HasJSONSchema.toSchema (α := TestNamedBranch)).checkRefsResolved

-- Composite types containing recursive inductives
#guard (HasJSONSchema.toSchema (α := TestWithRecursive)).checkRefsResolved

-- Non-recursive types trivially pass (no refNames at all)
#guard (HasJSONSchema.toSchema (α := TestPerson)).checkRefsResolved
#guard (HasJSONSchema.toSchema (α := TestColor)).checkRefsResolved
#guard (HasJSONSchema.toSchema (α := TestValue)).checkRefsResolved

-- ============================================================================
-- Negative validation tests: verify validation FAILS on invalid JSON
-- ============================================================================

private def isError (r : Except ValidationError Unit) : Bool :=
  match r with | .error _ => true | .ok _ => false

#guard isError (validateJson (HasJSONSchema.toSchema (α := TestPerson)) (.str "wrong"))
#guard isError (validateJson (HasJSONSchema.toSchema (α := TestPerson)) .null)
#guard isError (validateJson (HasJSONSchema.toSchema (α := TestColor)) (.str "purple"))
#guard isError (validateJson (HasJSONSchema.toSchema (α := TestColor)) (.num 42))
#guard isError (validateJson (HasJSONSchema.toSchema (α := TestValue)) (.str "notAVariant"))
#guard isError (validateJson (HasJSONSchema.toSchema (α := TestPeano)) (.num 1))

-- ============================================================================
-- Soundness theorem application examples
-- ============================================================================

example : validateJson
    (stringSchema (enum := some ["admin", "user", "guest"])) (.str "admin")
    = .ok () := by
  apply validateJson_stringEnum_mem; decide

example : validateJson stringSchema (.str "hello") = .ok () := by
  apply validateJson_stringSchema

example : validateJson booleanSchema (.bool true) = .ok () := by
  apply validateJson_booleanSchema

example : validateJson integerSchema (.num 42) = .ok () := by
  apply validateJson_integerSchema

example : validateJson numberSchema (.num 3.14) = .ok () := by
  apply validateJson_numberSchema

example : validateJson (integerSchema (some 0) (some 100)) (.num 50) = .ok () := by
  apply validateJson_integerSchema_range; native_decide

example : validateJson (numberSchema (some 0) (some 100)) (.num 50) = .ok () := by
  apply validateJson_numberSchema_range; native_decide

example : validateJson (arraySchema stringSchema)
    (.arr #[.str "a", .str "b", .str "c"]) = .ok () := by
  apply validateJson_arraySchema_correct; native_decide

example : validateJson
    (objectSchema
      [("name", stringSchema), ("age", integerSchema), ("active", booleanSchema)]
      ["name", "age", "active"])
    (Json.mkObj [("name", .str "Alice"), ("age", .num 30), ("active", .bool true)])
    = .ok () := by
  apply validateJson_objectSchema_correct <;> native_decide

example : validateJson
    (oneOfSchema [stringSchema, integerSchema, booleanSchema])
    (.str "hello")
    = .ok () := by
  apply validateJson_oneOfSchema_correct (s := stringSchema) (refName := none)
  · exact List.Mem.head _
  · native_decide

end JsonSchema.DeriveSchemaValid.Test
