import Mathlib.Data.Finmap
import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Set.Finite.Basic

/-!
# Finite maps and paper map notation

The generic finite-map layer: lookup, domain, insertion, deletion,
right-biased merge, restriction, and the paper's `⊎`, `↾`, `[↦]`, `∖`
notation with their lemmas. Nothing here depends on `Signature`.
-/

namespace Incr

noncomputable section

abbrev FMap (K V : Type) := Finmap (fun _ : K => V)

/-- `filterMap` output keys are a sub-multiset of the input keys. This is the
nodup-preservation fact behind `FMap.filterMap`. -/
private theorem filterMap_le_map_of {α β : Type} (f : α → Option β) (g : α → β)
    (s : Multiset α) (h : ∀ x, f x = none ∨ f x = some (g x)) :
    s.filterMap f ≤ s.map g := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      rcases hfa : f a with _ | b
      · rw [Multiset.filterMap_cons_none _ _ hfa, Multiset.map_cons]
        exact le_trans ih (Multiset.le_cons_self _ _)
      · have hb : b = g a := by
          rcases h a with h | h
          · rw [h] at hfa
            exact absurd hfa (by simp)
          · rw [hfa] at h
            exact Option.some.inj h
        subst hb
        rw [Multiset.filterMap_cons_some _ _ _ hfa, Multiset.map_cons]
        exact Multiset.cons_le_cons _ ih

namespace FMap

variable {K V W : Type}

/-- Computable lookup. -/
def get [DecidableEq K] (m : FMap K V) (k : K) : Option V := m.lookup k

/-- The key set as a proposition. -/
def dom (m : FMap K V) : Set K := {k | k ∈ m.keys}

/-- The key set as a finite set, for computable membership tests. -/
def keys (m : FMap K V) : Finset K := Finmap.keys m

/-- Computable insertion. -/
def set [DecidableEq K] (m : FMap K V) (k : K) (v : V) : FMap K V := m.insert k v

/-- Computable key removal. -/
def erase [DecidableEq K] (m : FMap K V) (k : K) : FMap K V := Finmap.erase k m

/-- Right-biased merge. Mathlib's union is left-biased, so the arguments are reversed. -/
def merge [DecidableEq K] (earlier later : FMap K V) : FMap K V := later ∪ earlier

/-- Keep the entries whose key satisfies `p`. Computable. -/
def filterKeys (p : K → Prop) [DecidablePred p] (m : FMap K V) : FMap K V where
  entries := m.entries.filter fun kv => p kv.1
  nodupKeys := by
    apply Multiset.nodup_keys.mp
    exact Multiset.nodup_of_le (Multiset.map_le_map (Multiset.filter_le _ _))
      m.nodupKeys.nodup_keys

/-- Map each entry to a new value, dropping entries that map to `none`. Computable. -/
def filterMap (f : K → V → Option W) (m : FMap K V) : FMap K W where
  entries := m.entries.filterMap fun kv : Sigma (fun _ : K => V) =>
    (f kv.1 kv.2).map fun w : W => (⟨kv.1, w⟩ : Sigma (fun _ : K => W))
  nodupKeys := by
    apply Multiset.nodup_keys.mp
    change (Multiset.map Sigma.fst (m.entries.filterMap
      (fun kv : Sigma (fun _ : K => V) =>
        (f kv.1 kv.2).map fun w : W =>
          (⟨kv.1, w⟩ : Sigma (fun _ : K => W))))).Nodup
    have hle : m.entries.filterMap
        (fun x : Sigma (fun _ : K => V) =>
          ((f x.1 x.2).map fun w : W =>
            (⟨x.1, w⟩ : Sigma (fun _ : K => W))).map Sigma.fst)
        ≤ m.entries.map Sigma.fst := by
      refine filterMap_le_map_of _ _ _ (fun x => ?_)
      rcases f x.1 x.2 with _ | w
      · exact Or.inl rfl
      · exact Or.inr rfl
    rw [Multiset.map_filterMap]
    exact Multiset.nodup_of_le hle m.nodupKeys.nodup_keys

/-- Keep only the entries whose key lies in `s`.
This ghost helper enumerates the map, so it stays `noncomputable`. -/
noncomputable def restrict (m : FMap K V) (s : Set K) : FMap K V := by
  classical
  exact filterKeys (fun k => k ∈ s) m

/-! ## Paper-style map notation -/

/-- `A ⊎ B` — paper staged patch union (model.tex:257, `\uplus`): right-biased
merge where new entries take precedence at shared paths. -/
notation:65 A:65 " ⊎ " B:66 => FMap.merge A B

/-- `m ↾ s` — paper map restriction (model.tex:292, `R ↾ (Path ∖ dom Δ)`):
keep only the entries whose key lies in `s`. -/
notation:65 M:65 " ↾ " S:66 => FMap.restrict M S

/-- `m[k ↦ v]` — paper map update (`buffer[i ↦ ⟨s'', open⟩]`): insert or
overwrite the entry at `k`. -/
notation:65 M:65 "[" k:max " ↦ " v:max "]" => FMap.set M k v

/-- `m ∖ k` — paper map removal (`buffer ∖ i`, `sandbox ∖ i`): remove the
entry at `k`. -/
notation:65 M:65 " ∖ " K:66 => FMap.erase M K

theorem get_filterKeys_eq_some [DecidableEq K] (p : K → Prop) [DecidablePred p] (m : FMap K V)
    (k : K) (v : V) : get (filterKeys p m) k = some v ↔ p k ∧ get m k = some v := by
  simp only [get, filterKeys, Finmap.lookup_eq_some_iff, Multiset.mem_filter, and_comm]

theorem get_filterKeys [DecidableEq K] (p : K → Prop) [DecidablePred p] (m : FMap K V) (k : K) :
    get (filterKeys p m) k = if p k then get m k else none := by
  apply Option.ext
  intro v
  rw [get_filterKeys_eq_some]
  by_cases hk : p k
  · simp [hk]
  · simp [hk]

theorem get_restrict_eq_some [DecidableEq K] (m : FMap K V) (s : Set K) (k : K) (v : V) :
    get (restrict m s) k = some v ↔ k ∈ s ∧ get m k = some v := by
  classical
  change get (filterKeys (fun k => k ∈ s) m) k = some v ↔ _
  exact get_filterKeys_eq_some _ _ _ _

theorem get_restrict [DecidableEq K] (m : FMap K V) (s : Set K) [DecidablePred (· ∈ s)]
    (k : K) :
    get (restrict m s) k = if k ∈ s then get m k else none := by
  apply Option.ext
  intro v
  rw [get_restrict_eq_some]
  by_cases hk : k ∈ s <;> simp [hk]

theorem restrict_congr [DecidableEq K] {m m' : FMap K V} {s : Set K}
    (h : ∀ q ∈ s, get m q = get m' q) :
    restrict m s = restrict m' s := by
  classical
  apply Finmap.ext_lookup
  intro q
  change get (restrict m s) q = get (restrict m' s) q
  rw [get_restrict, get_restrict]
  by_cases hq : q ∈ s
  · simp [hq, h q hq]
  · simp [hq]

theorem filterKeys_dom_subset (p : K → Prop) [DecidablePred p]
    (m : FMap K V) : dom (filterKeys p m) ⊆ dom m := by
  classical
  intro q hq
  obtain ⟨v, hv⟩ := Finmap.mem_iff.mp (Finmap.mem_keys.mp hq)
  obtain ⟨-, hv⟩ := (get_filterKeys_eq_some p m q v).mp hv
  exact Finmap.mem_keys.mpr (Finmap.mem_iff.mpr ⟨v, hv⟩)

theorem mem_dom_merge [DecidableEq K] {a b : FMap K V} {q : K}
    (h : q ∈ dom (merge a b)) : q ∈ dom a ∪ dom b := by
  have h' : q ∈ merge a b := Finmap.mem_keys.mp h
  have h'' : q ∈ b ∪ a := h'
  rw [Finmap.mem_union] at h''
  rcases h'' with h'' | h''
  · exact Or.inr (Finmap.mem_keys.mpr h'')
  · exact Or.inl (Finmap.mem_keys.mpr h'')

theorem dom_merge [DecidableEq K] (a b : FMap K V) : dom (merge a b) = dom a ∪ dom b := by
  ext q
  constructor
  · exact mem_dom_merge
  · intro hq
    rcases hq with h | h
    · exact Finmap.mem_keys.mpr (Finmap.mem_union.mpr (Or.inr (Finmap.mem_keys.mp h)))
    · exact Finmap.mem_keys.mpr (Finmap.mem_union.mpr (Or.inl (Finmap.mem_keys.mp h)))

theorem get_filterMap_eq_some [DecidableEq K] (f : K → V → Option W) (m : FMap K V) (k : K)
    (w : W) : get (filterMap f m) k = some w ↔ ∃ v, get m k = some v ∧ f k v = some w := by
  simp only [get, filterMap, Finmap.lookup_eq_some_iff, Multiset.mem_filterMap]
  constructor
  · rintro ⟨kv, hkv, hmap⟩
    obtain ⟨a, hfv, hw⟩ := Option.map_eq_some_iff.mp hmap
    cases hw
    exact ⟨kv.2, hkv, hfv⟩
  · rintro ⟨v, hv, hfv⟩
    exact ⟨⟨k, v⟩, hv, Option.map_eq_some_iff.mpr ⟨w, hfv, rfl⟩⟩

theorem get_filterMap [DecidableEq K] (f : K → V → Option W) (m : FMap K V) (k : K) :
    get (filterMap f m) k = (get m k).bind (f k) := by
  apply Option.ext
  intro w
  rw [get_filterMap_eq_some]
  cases h : get m k with
  | none => simp
  | some v => simp

theorem get_merge_of_mem [DecidableEq K] (earlier later : FMap K V) (k : K) (v : V)
    (h : get later k = some v) : get (merge earlier later) k = some v := by
  rw [show get (merge earlier later) k = get later k from
    Finmap.lookup_union_left (Finmap.mem_iff.mpr ⟨v, by simpa only [FMap.get] using h⟩)]
  exact h

theorem get_merge_of_not_mem [DecidableEq K] (earlier later : FMap K V) (k : K)
    (h : get later k = none) : get (merge earlier later) k = get earlier k :=
  Finmap.lookup_union_right (Finmap.lookup_eq_none.mp h)

theorem mem_keys_iff (m : FMap K V) (k : K) : k ∈ keys m ↔ k ∈ m := Finmap.mem_keys

/-- `FMap.get` gives `none` exactly when the key is absent.
This is the single named entry point for the `get` unfolding.
Keep `get` definitions behind this lemma. -/
theorem get_eq_none [DecidableEq K] {m : FMap K V} {k : K} :
    get m k = none ↔ k ∉ m := by
  rw [get, Finmap.lookup_eq_none]

/-- If the keys of `m` lie in `s`, and `s` is disjoint from `t`, then a key of `t`
is absent from `m`. Centralizes the `get = none` bookkeeping proofs. -/
theorem get_eq_none_of_disjoint [DecidableEq K] {m : FMap K V} {s t : Set K}
    (hdisj : Disjoint s t) (hsub : ∀ k ∈ dom m, k ∈ s) (hk : k ∈ t) :
    get m k = none := by
  rw [get_eq_none]
  exact fun hmem => Set.disjoint_left.mp hdisj (hsub _ (Finmap.mem_keys.mpr hmem)) hk

/-- Get-set at the same key. -/
theorem get_set_self {K V} [DecidableEq K] {m : FMap K V} {k : K} {v : V} :
    FMap.get (m[k ↦ v]) k = some v :=
  Finmap.lookup_insert m

/-- Get-set at a different key. -/
theorem get_set_other {K V} [DecidableEq K] {m : FMap K V} {j k : K} {v : V}
    (h : j ≠ k) : FMap.get (m[k ↦ v]) j = FMap.get m j :=
  Finmap.lookup_insert_of_ne m h

/-- Get-erase at a different key. -/
theorem get_erase_of_ne {K V} [DecidableEq K] {m : FMap K V} {j k : K}
    (h : j ≠ k) : FMap.get (m ∖ k) j = FMap.get m j :=
  Finmap.lookup_erase_ne h

/-- Get-erase at the same key. -/
theorem get_erase_self {K V} [DecidableEq K] {m : FMap K V} {k : K} :
    FMap.get (m ∖ k) k = none :=
  Finmap.lookup_erase _ _

@[simp] theorem dom_empty {K V : Type} : dom (∅ : FMap K V) = (∅ : Set K) := by
  ext k
  simp [dom]

theorem dom_set_of_get [DecidableEq K] (m : FMap K V) (k : K) (v : V)
    (h : ∃ w, get m k = some w) : dom (set m k v) = dom m := by
  ext q
  change q ∈ Finmap.insert k v m ↔ q ∈ m
  rw [Finmap.mem_insert]
  constructor
  · rintro (rfl | hq)
    · obtain ⟨w, hw⟩ := h
      exact Finmap.mem_iff.mpr ⟨w, by simpa only [get] using hw⟩
    · exact hq
  · exact Or.inr

theorem dom_set_of_mem [DecidableEq K] (m : FMap K V) (k : K) (v : V)
    (h : k ∈ dom m) : dom (set m k v) = dom m := by
  apply dom_set_of_get
  exact Finmap.mem_iff.mp (Finmap.mem_keys.mpr h)

theorem dom_erase [DecidableEq K] (m : FMap K V) (k : K) :
    dom (erase m k) = {q | q ∈ dom m ∧ q ≠ k} := by
  ext q
  simp [dom, erase, Finmap.mem_keys, and_comm]

theorem merge_empty_earlier [DecidableEq K] (m : FMap K V) : merge ∅ m = m := by
  apply Finmap.ext_lookup
  intro k
  change Finmap.lookup k (m ∪ (∅ : FMap K V)) = Finmap.lookup k m
  by_cases hk : k ∈ m
  · exact Finmap.lookup_union_left hk
  · rw [Finmap.lookup_union_right hk, Finmap.lookup_empty, Finmap.lookup_eq_none.mpr hk]

theorem filterKeys_true (p : K → Prop) [DecidablePred p] (m : FMap K V)
    (hp : ∀ k, p k) : filterKeys p m = m := by
  classical
  apply Finmap.ext_lookup
  intro k
  change FMap.get (filterKeys p m) k = FMap.get m k
  rw [get_filterKeys, ite_eq_left (hp k)]

@[simp] theorem filterKeys_keys_empty [DecidableEq K] {W : Type} (m : FMap K V) :
    filterKeys (fun q => q ∉ keys (∅ : FMap K W)) m = m :=
  filterKeys_true _ _ (fun q => by simp [FMap.keys])

theorem eq_empty_of_dom_eq_empty (m : FMap K V) (h : dom m = ∅) : m = ∅ := by
  classical
  apply Finmap.ext_lookup
  intro k
  rw [Finmap.lookup_empty, Finmap.lookup_eq_none]
  intro hk
  obtain ⟨v, hv⟩ := Finmap.mem_iff.mp hk
  have hk' : k ∈ dom m :=
    Finmap.mem_keys.mpr (Finmap.mem_iff.mpr ⟨v, hv⟩)
  rw [h] at hk'
  exact hk'

end FMap

end

end Incr
