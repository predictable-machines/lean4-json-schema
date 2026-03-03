import JsonSchema.Schema

namespace JsonSchema

-- ══════════════════════════════════════════════════════════════
-- Serialization properties for $defs/$ref
-- ══════════════════════════════════════════════════════════════

-- Ref resolution is handled at the JSONSchema level (collectRefDefs,
-- collectAllRefNames, checkRefsResolved in Schema.lean), not on serialized Json.
-- Earlier JSON-level helpers (collectJsonRefs, collectJsonDefKeys, refUriToName)
-- were removed because they were unused — the schema-level approach is both
-- total (no fuel parameter) and directly usable in proofs.

/-- The serialization invariant: every refName in the schema tree has a corresponding
    definition site (refName + oneOf) found by `collectRefDefs`. This guarantees that
    `toLeanJson` will produce a `$defs` entry for every `$ref` pointer.
    The precondition `checkRefsResolved` is decidable and verified computationally
    on all concrete types via `#guard` tests (see Test/DeriveTest.lean).
    The original bug — composite types (e.g., SpecSchema containing TypeExpr) emitting
    `$ref` pointers with no corresponding `$defs` entries — is caught by this check. -/
theorem allRefsResolved (schema : JSONSchema) (h : schema.checkRefsResolved = true)
    : ∀ name ∈ collectAllRefNames schema,
        name ∈ (collectRefDefs schema).map Prod.fst := by
  unfold JSONSchema.checkRefsResolved at h
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  exact h

end JsonSchema
