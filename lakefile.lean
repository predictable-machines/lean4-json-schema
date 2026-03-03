import Lake
open Lake DSL

package «json-schema» where
  version := v!"0.1.0"

@[default_target]
lean_lib JsonSchema where
  roots := #[`JsonSchema]
