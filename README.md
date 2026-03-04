# lean4-json-schema

A Lean 4 library for [JSON Schema](https://json-schema.org/) with types, validation, correctness proofs, and type class deriving handlers.

> [!WARNING]
> This library is under active development and **does not yet fully cover the JSON Schema standard**. We are actively using it to build [Predictable Code](https://predictablemachines.com/tools/predictable-code/), but the API surface, type definitions, and proof interfaces may change without notice. The current correctness proofs might not cover the full extent of the functionality provided in the library. Use at your own discretion.

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
