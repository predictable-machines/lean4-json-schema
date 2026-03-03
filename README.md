# lean4-json-schema

A Lean 4 library for JSON Schema — types, validation, correctness proofs, and deriving handlers.

## Features

- **Schema Types**: `JSONSchema` inductive type with full JSON Schema support (`SchemaKind`, `HasJSONSchema` typeclass)
- **Validation**: Total (non-partial) `validateJson` function for runtime validation against schemas
- **Correctness Proofs**: Soundness and completeness theorems, bridge theorems connecting schema derivation to validation
- **Deriving Handlers**: `deriving HasJSONSchema` and `deriving ValidatesAgainstSchema` for enums, structures, and inductives (including recursive types with `$defs`/`$ref`)

## Usage

Add to your `lakefile.lean`:

```lean
require «json-schema» from git
  "https://github.com/predictable-machines/lean4-json-schema" @ "v0.1.0"
```

Then import in your Lean files:

```lean
import JsonSchema

-- Derive schema for a structure
structure Person where
  name : String
  age : Nat
  deriving HasJSONSchema

-- Derive validation proof
structure Person where
  name : String
  age : Nat
  deriving HasJSONSchema, ValidatesAgainstSchema

-- Validate JSON at runtime
#eval validateJson (HasJSONSchema.schema Person) (Lean.Json.mkObj [("name", "Alice"), ("age", 30)])
```

## Building

```bash
lake build
```

## License

MIT
