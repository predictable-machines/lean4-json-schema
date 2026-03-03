import JsonSchema.Schema
import JsonSchema.Validation
import JsonSchema.Correctness.Soundness
import Std.Data.TreeMap.Raw.Lemmas

namespace JsonSchema

open Lean (Json JsonNumber ToJson toJson)

-- ============================================================================
-- Bridge lemmas for Json.mkObj + structure composition
-- ============================================================================

-- TreeMap.Raw.ofList produces a well-formed tree (needed by many TreeMap lemmas).
-- Uses Std.DTreeMap.Internal.Impl.WF.constInsertMany — an internal Std API that
-- may break across Lean/Std updates. Pinned to Std from Lean v4.28.0.
-- TODO: replace with a public API when Std exposes one (track on toolchain upgrades).
private theorem ofList_wf (l : List (String × Json))
    : (Std.TreeMap.Raw.ofList l compare).WF := by
  simp only [Std.TreeMap.Raw.ofList, Std.DTreeMap.Raw.Const.ofList,
             Std.DTreeMap.Internal.Impl.Const.ofList]
  exact ⟨⟨Std.DTreeMap.Internal.Impl.WF.constInsertMany
    (ρ := List (String × Json)) .empty⟩⟩

/-- Lift a key-only Pairwise condition to a pair-level condition.
    `decide` works on concrete key lists but not on pairs with abstract values. -/
private theorem pairwiseKeys (pairs : List (String × Json))
    (h : (pairs.map Prod.fst).Pairwise (fun a b => ¬compare a b = .eq))
    : List.Pairwise (fun a b => ¬compare a.1 b.1 = .eq) pairs := by
  induction pairs with
  | nil => exact List.Pairwise.nil
  | cons p rest ih =>
    rw [List.map_cons, List.pairwise_cons] at h
    rw [List.pairwise_cons]
    exact ⟨fun b hb => h.1 b.1 (List.mem_map.mpr ⟨b, hb, rfl⟩), ih h.2⟩

/-- checkRequired succeeds when every required key has a value in the pairs list. -/
private theorem checkRequired_ofList
    (req : List String) (pairs : List (String × Json))
    (hPw : List.Pairwise (fun a b => ¬compare a.1 b.1 = .eq) pairs)
    (hReq : ∀ r ∈ req, ∃ v, (r, v) ∈ pairs)
    : checkRequired req (Json.obj (Std.TreeMap.Raw.ofList pairs compare)) = .ok () := by
  induction req with
  | nil => simp [checkRequired]
  | cons r rs ih =>
    unfold checkRequired
    simp only [Json.getObjVal?]
    obtain ⟨v, hv⟩ := hReq r (List.Mem.head _)
    rw [Std.TreeMap.Raw.get?_eq_getElem?]
    rw [Std.TreeMap.Raw.getElem?_ofList_of_mem (k := r) (k' := r)
      Std.ReflCmp.compare_self hPw hv]
    simp only
    exact ih (fun r' hr' => hReq r' (List.Mem.tail _ hr'))

/-- checkUnknownFields succeeds when every field key has a corresponding schema in props. -/
private theorem checkUnknownFields_subset
    (fields : List (String × Json)) (props : List (String × JSONSchema))
    (h : ∀ p ∈ fields, ∃ s, (p.1, s) ∈ props)
    : checkUnknownFields fields props = .ok () := by
  induction fields with
  | nil => simp [checkUnknownFields]
  | cons f rest ih =>
    simp only [checkUnknownFields]
    obtain ⟨s, hs⟩ := h f (List.Mem.head _)
    have hfind : (props.find? (fun p => p.1 == f.1)).isSome := by
      rw [List.find?_isSome]; exact ⟨(f.1, s), hs, by simp⟩
    rw [Option.isSome_iff_exists] at hfind
    obtain ⟨val, hval⟩ := hfind; rw [hval]
    exact ih (fun p hp => h p (List.Mem.tail _ hp))

/-- Keys in the tree's toList are a subset of the original input keys. -/
private theorem toList_keys_of_ofList (pairs : List (String × Json))
    : ∀ p ∈ (Std.TreeMap.Raw.ofList pairs compare).toList,
      p.1 ∈ pairs.map Prod.fst := by
  intro ⟨k, v⟩ hmem; simp only
  rw [Std.TreeMap.Raw.mem_toList_iff_getElem?_eq_some (ofList_wf pairs)] at hmem
  have hcontains : (Std.TreeMap.Raw.ofList pairs compare).contains k := by
    rw [← Std.TreeMap.Raw.isSome_getElem?_eq_contains (ofList_wf pairs), hmem]; rfl
  rw [Std.TreeMap.Raw.contains_ofList] at hcontains
  exact List.mem_of_elem_eq_true hcontains

/-- checkUnknownFields on ofList's toList succeeds when all pair keys appear in props. -/
private theorem checkUnknownFields_ofList
    (props : List (String × JSONSchema)) (pairs : List (String × Json))
    (hKeys : ∀ k ∈ pairs.map Prod.fst, k ∈ props.map Prod.fst)
    : checkUnknownFields (Std.TreeMap.Raw.ofList pairs compare).toList props
      = .ok () := by
  apply checkUnknownFields_subset
  intro p hp
  have hk' := hKeys p.1 (toList_keys_of_ofList pairs p hp)
  obtain ⟨⟨name, schema⟩, hmem, rfl⟩ := (List.mem_map (f := Prod.fst)).mp hk'
  exact ⟨schema, hmem⟩

/-- validateProps succeeds on ofList's toList when every field in pairs validates
    against its corresponding schema. -/
private theorem validateProps_ofList
    (props : List (String × JSONSchema)) (pairs : List (String × Json))
    (hPw : List.Pairwise (fun a b => ¬compare a.1 b.1 = .eq) pairs)
    (hValid : ∀ name schema, (name, schema) ∈ props →
      ∀ v, (name, v) ∈ pairs → validateJson schema v = .ok ())
    : validateProps props (Std.TreeMap.Raw.ofList pairs compare).toList
      = .ok () := by
  induction props with
  | nil => simp [validateProps]
  | cons p rest ih =>
    obtain ⟨name, schema⟩ := p
    simp only [validateProps]
    cases hFind : (Std.TreeMap.Raw.ofList pairs compare).toList.find?
        (fun x => x.1 == name) with
    | none =>
      exact ih (fun n s hns v hv => hValid n s (List.Mem.tail _ hns) v hv)
    | some val =>
      obtain ⟨k, v⟩ := val
      have hpred := List.find?_some hFind
      have hkeq : k = name := eq_of_beq hpred
      -- Reduce match some (k, v) with | some (_, value) => ...
      simp only
      -- (k, v) is in toList → tree maps k ↦ v
      have hmem := List.mem_of_find?_eq_some hFind
      rw [Std.TreeMap.Raw.mem_toList_iff_getElem?_eq_some (ofList_wf pairs)] at hmem
      have hcontains : (Std.TreeMap.Raw.ofList pairs compare).contains k := by
        rw [← Std.TreeMap.Raw.isSome_getElem?_eq_contains (ofList_wf pairs), hmem]; rfl
      rw [Std.TreeMap.Raw.contains_ofList] at hcontains
      have hInPairs := List.mem_of_elem_eq_true hcontains
      obtain ⟨⟨k', v'⟩, hv'mem, hk'eq⟩ := (List.mem_map (f := Prod.fst)).mp hInPairs
      -- hk'eq : Prod.fst (k', v') = k, i.e. k' = k
      change k' = k at hk'eq
      rw [hk'eq] at hv'mem
      -- Now hv'mem : (k, v') ∈ pairs
      have hv'eq := Std.TreeMap.Raw.getElem?_ofList_of_mem (k := k) (k' := k)
        Std.ReflCmp.compare_self hPw hv'mem
      -- hmem : [k]? = some v; hv'eq : [k]? = some v'
      rw [hv'eq] at hmem; cases hmem
      -- v = v'; use hkeq (k = name) to align with hValid
      rw [hkeq] at hv'mem
      rw [hValid name schema (List.Mem.head _) v hv'mem]
      exact ih (fun n s hns v'' hv'' => hValid n s (List.Mem.tail _ hns) v'' hv'')

/-- Main bridge theorem: validates an object schema against Json.mkObj.
    This is the key composition theorem used by the derive handler for structures. -/
theorem validateJson_mkObj_objectSchema
    (props : List (String × JSONSchema))
    (req : List String)
    (pairs : List (String × Json))
    (hPw : (pairs.map Prod.fst).Pairwise (fun a b => ¬compare a b = .eq))
    (hReq : ∀ r ∈ req, ∃ v, (r, v) ∈ pairs)
    (hKeys : ∀ k ∈ pairs.map Prod.fst, k ∈ props.map Prod.fst)
    (hValid : ∀ name schema, (name, schema) ∈ props →
      ∀ v, (name, v) ∈ pairs → validateJson schema v = .ok ())
    : validateJson (objectSchema props req) (Json.mkObj pairs) = .ok () := by
  show validateJson (objectSchema props req)
    (Json.obj (Std.TreeMap.Raw.ofList pairs compare)) = .ok ()
  have hPwPairs := pairwiseKeys pairs hPw
  exact validateJson_objectSchema_correct props req _
    (checkRequired_ofList req pairs hPwPairs hReq)
    (checkUnknownFields_ofList props pairs hKeys)
    (validateProps_ofList props pairs hPwPairs hValid)

/-- Helper for derive handler: when pair keys match required keys, hReq is trivially satisfied.
    Lets us discharge hReq with `rfl` instead of case-splitting on membership. -/
theorem hReq_of_map_fst
    (req : List String) (pairs : List (String × Json))
    (h : req = pairs.map Prod.fst)
    : ∀ r ∈ req, ∃ v, (r, v) ∈ pairs := by
  intro r hr
  rw [h] at hr
  obtain ⟨⟨_, v⟩, hmem, rfl⟩ := List.mem_map.mp hr
  exact ⟨v, hmem⟩

end JsonSchema
