import Lean.Data.Json
import JsonSchema.Schema

namespace JsonSchema

open Lean (Json JsonNumber)

/-- Strict less-than on `JsonNumber` (value = mantissa / 10^exponent).
    Cross-multiplies to a common denominator so it handles decimals correctly. -/
def jsonNumberLt (a b : JsonNumber) : Bool :=
  a.mantissa * (10 : Int) ^ b.exponent < b.mantissa * (10 : Int) ^ a.exponent

inductive ValidationError where
  | typeMismatch (expected : String) (actual : String) : ValidationError
  | missingRequired (field : String) : ValidationError
  | unknownProperty (field : String) : ValidationError
  | outOfRange (value : JsonNumber) (min : Option JsonNumber) (max : Option JsonNumber) : ValidationError
  | invalidEnum (field : String) (value : String) (allowed : List String) : ValidationError
  | arrayItemInvalid (index : Nat) (error : ValidationError) : ValidationError
  | propertyInvalid (field : String) (error : ValidationError) : ValidationError
  | oneOfNoMatch : ValidationError
  deriving Repr, DecidableEq

namespace ValidationError

def toString : ValidationError → String
  | typeMismatch expected actual => s!"Type mismatch: expected {expected}, got {actual}"
  | missingRequired field => s!"Missing required field: {field}"
  | unknownProperty field => s!"Unknown property: {field}"
  | outOfRange value min max =>
      let minStr := min.map (fun m => s!"min={m}") |>.getD ""
      let maxStr := max.map (fun m => s!"max={m}") |>.getD ""
      let range := if minStr.isEmpty && maxStr.isEmpty then "" else s!" (expected {minStr} {maxStr})"
      s!"Value {value} out of range{range}"
  | invalidEnum field value allowed => s!"Invalid enum value '{value}' for field {field}. Allowed: {allowed}"
  | arrayItemInvalid index error => s!"Invalid array item at index {index}: {toString error}"
  | propertyInvalid field error => s!"Invalid property '{field}': {toString error}"
  | oneOfNoMatch => "No schema in oneOf matched"

instance : ToString ValidationError where
  toString := ValidationError.toString

end ValidationError

def jsonTypeName : Json → String
  | .null => "null"
  | .bool _ => "boolean"
  | .num _ => "number"
  | .str _ => "string"
  | .arr _ => "array"
  | .obj _ => "object"

/-- Validate a number against optional min/max bounds -/
def validateRange (n : JsonNumber) (min max : Option JsonNumber)
    : Except ValidationError Unit :=
  match (min, max) with
  | (some lo, some hi) =>
      if jsonNumberLt n lo || jsonNumberLt hi n then
        .error (.outOfRange n (some lo) (some hi))
      else .ok ()
  | (some lo, none) =>
      if jsonNumberLt n lo then .error (.outOfRange n (some lo) none)
      else .ok ()
  | (none, some hi) =>
      if jsonNumberLt hi n then .error (.outOfRange n none (some hi))
      else .ok ()
  | (none, none) => .ok ()

/-- Check that all required fields exist in the JSON object -/
def checkRequired (required : List String) (json : Json)
    : Except ValidationError Unit :=
  match required with
  | [] => .ok ()
  | field :: rest =>
      match json.getObjVal? field with
      | .error _ => .error (.missingRequired field)
      | .ok _ => checkRequired rest json

/-- Reject JSON fields not present in the schema properties -/
def checkUnknownFields (fields : List (String × Json))
    (props : List (String × JSONSchema)) : Except ValidationError Unit :=
  match fields with
  | [] => .ok ()
  | (fieldName, _) :: rest =>
      match props.find? (fun (name, _) => name == fieldName) with
      | some _ => checkUnknownFields rest props
      | none => .error (.unknownProperty fieldName)

mutual
/-- Validate JSON against a schema. Total (no `partial`) so it can be used in proofs. -/
def validateJson (schema : JSONSchema) (json : Json) : Except ValidationError Unit :=
  match schema.kind with
  | .string =>
      match json with
      | .str s =>
          match schema.enum with
          | some allowed =>
              if allowed.contains s then .ok ()
              else .error (.invalidEnum "" s allowed)
          | none => .ok ()
      | _ => .error (.typeMismatch "string" (jsonTypeName json))

  | .integer =>
      match json with
      | .num n => validateRange n schema.minimum schema.maximum
      | _ => .error (.typeMismatch "integer" (jsonTypeName json))

  | .number =>
      match json with
      | .num n => validateRange n schema.minimum schema.maximum
      | _ => .error (.typeMismatch "number" (jsonTypeName json))

  | .boolean =>
      match json with
      | .bool _ => .ok ()
      | _ => .error (.typeMismatch "boolean" (jsonTypeName json))

  | .array =>
      match json with
      | .arr items =>
          match _hpi : schema.prefixItems with
          | some prefixSchemas =>
              match validatePrefixItems prefixSchemas items.toList 0 with
              | .error e => .error e
              | .ok () =>
                  match _hi : schema.items with
                  | some itemSchema =>
                      validateArrayItems itemSchema (items.toList.drop prefixSchemas.length) 0
                  | none => .ok ()
          | none =>
              match _hi : schema.items with
              | some itemSchema => validateArrayItems itemSchema items.toList 0
              | none => .ok ()
      | _ => .error (.typeMismatch "array" (jsonTypeName json))

  | .object =>
      match json with
      | .obj obj =>
          match checkRequired schema.required json with
          | .error e => .error e
          | .ok () =>
            match _hp : schema.properties with
            | some props =>
                match checkUnknownFields obj.toList props with
                | .error e => .error e
                | .ok () => validateProps props obj.toList
            | none => .ok ()
      | _ => .error (.typeMismatch "object" (jsonTypeName json))

  | .null =>
      match json with
      | .null => .ok ()
      | _ => .error (.typeMismatch "null" (jsonTypeName json))

  | .any => .ok ()

  | .oneOf =>
      match _ho : schema.oneOf with
      | some schemas => validateOneOfSchemas schemas json
      | none => .ok ()
termination_by (sizeOf schema, 0)
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := JSONSchema.sizeOf_items_lt _ _ _hi; omega)
    | (have := JSONSchema.sizeOf_prefixItems_lt _ _ _hpi; omega)
    | (have := JSONSchema.sizeOf_properties_lt _ _ _hp; omega)
    | (have := JSONSchema.sizeOf_oneOf_lt _ _ _ho; omega)

/-- Validate array items against positional schemas (JSON Schema prefixItems). -/
def validatePrefixItems (schemas : List JSONSchema) (items : List Json) (idx : Nat)
    : Except ValidationError Unit :=
  match schemas with
  | [] => .ok ()
  | s :: ss =>
      match items with
      -- Reuses `typeMismatch` for an arity error; a dedicated `tooFewItems` variant
      -- would be cleaner but is low priority since prefixItems is only used internally.
      | [] => .error (.typeMismatch s!"at least {idx + 1} array items" s!"{idx} items")
      | item :: rest =>
          match validateJson s item with
          | .error e => .error (.arrayItemInvalid idx e)
          | .ok () => validatePrefixItems ss rest (idx + 1)
termination_by (sizeOf schemas, sizeOf items + 1)
decreasing_by all_goals simp_wf; omega

/-- Validate each item in a JSON array against the item schema -/
def validateArrayItems (itemSchema : JSONSchema) (items : List Json) (idx : Nat)
    : Except ValidationError Unit :=
  match items with
  | [] => .ok ()
  | item :: rest =>
      match validateJson itemSchema item with
      | .error e => .error (.arrayItemInvalid idx e)
      | .ok () => validateArrayItems itemSchema rest (idx + 1)
termination_by (sizeOf itemSchema, sizeOf items + 1)
decreasing_by all_goals simp_wf; omega

/-- Validate each schema property against the corresponding JSON field.
    Missing fields are OK — required fields are checked separately by `checkRequired`. -/
def validateProps (props : List (String × JSONSchema)) (obj : List (String × Json))
    : Except ValidationError Unit :=
  match props with
  | [] => .ok ()
  | (name, propSchema) :: rest =>
      match obj.find? (fun (k, _) => k == name) with
      | some (_, value) =>
          match validateJson propSchema value with
          | .error e => .error (.propertyInvalid name e)
          | .ok () => validateProps rest obj
      | none => validateProps rest obj
termination_by (sizeOf props, 0)
decreasing_by all_goals simp_wf; omega

/-- Check if at least one sub-schema in a oneOf validates the JSON.
    Note: this implements "anyOf" semantics (first match wins), not strict JSON Schema
    "oneOf" (exactly one must match). This is sufficient because our derived `toJson`
    instances produce values that match exactly one branch deterministically. -/
def validateOneOfSchemas (schemas : List JSONSchema) (json : Json)
    : Except ValidationError Unit :=
  match schemas with
  | [] => .error .oneOfNoMatch
  | s :: rest =>
      match validateJson s json with
      | .ok () => .ok ()
      | .error _ => validateOneOfSchemas rest json
termination_by (sizeOf schemas, 0)
decreasing_by all_goals simp_wf; omega
end

def validate (schema : JSONSchema) (json : Json) : Except String Unit :=
  match validateJson schema json with
  | .ok _ => .ok ()
  | .error e => .error (toString e)

end JsonSchema
