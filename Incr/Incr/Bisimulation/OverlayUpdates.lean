import Incr.Incr.Bisimulation.StepMatching
import Incr.Incr.Bisimulation.PrefixProperties
import Incr.Incr.Math.PatchAlgebra
import Incr.Incr.Bisimulation.Basis

/-! # `thm:paper-bisimulation`: staged-patch disjointness and post-step overlay
algebra -/

open Incr
namespace Incr.Incr.OverlayUpdates
noncomputable section
variable {sig : Signature} {m : CommandModel sig} {h : Host sig} {prog : sig.Prog}

theorem disjoint_of_slices {trace : Trace m h .incr prog} {w : World sig}
    {current : Option (Nat × PipelineInit sig)}
    (slices : LiveSliceProperties trace w current) (isolated : Isolated trace) :
    PendingDisjoint w := by
  intro i j sb other different hi hj
  obtain ⟨entry, init, he, si, _⟩ := slices i sb hi
  obtain ⟨entry', init', he', sj, _⟩ := slices j other hj
  have same := Option.some.inj (he.symm.trans he')
  cases same
  rw [← si.1, ← sj.1]
  exact (isolated entry i j different).mono_right Set.subset_union_right

theorem disjoint_of_state {trace : Trace m h .incr prog} {w : World sig}
    (state : SandboxState trace w) (isolated : Isolated trace) : PendingDisjoint w := by
  intro i j sb other different hi hj
  obtain ⟨entry, init, he, hw, _⟩ := PrefixProperties.live_paths state hi
  obtain ⟨entry', init', he', hw', _⟩ := PrefixProperties.live_paths state hj
  have same := Option.some.inj (he.symm.trans he')
  cases same
  rw [← hw, ← hw']
  exact (isolated entry i j different).mono_right Set.subset_union_right

theorem selection_disjoint {executor : Executor} {trace : Trace m h executor prog}
    {before selected : World sig} {selection : Selection sig}
    (discipline : SelectionDiscipline trace before selection selected)
    (old : PendingDisjoint before) : PendingDisjoint selected := by
  obtain ⟨_, _, _, init, _⟩ := discipline
  cases hi : selection.init with
  | none =>
    simp only [hi] at init
    intro i j sb other different hs ht
    rw [init.1] at hs ht
    exact old i j sb other different hs ht
  | some initialization =>
    simp only [hi] at init
    intro i j sb other different hs ht
    rw [init.2.2.2.2] at hs ht
    have hs' := initialSandboxes_get_eq initialization before.fs hs
    rw [hs']
    simp [Sandbox.initial]

theorem pending_none (w : World sig) (q : sig.Path)
    (absent : ∀ i sb, FMap.get w.sandbox i = some sb → FMap.get sb.patch q = none) :
    FMap.get (pendingPatch w) q = none := by
  classical
  have fold (slots : List Nat) (acc : Patch sig) :
      FMap.get (slots.foldl (fun acc i => match FMap.get w.sandbox i with
        | none => acc | some sb => acc ⊎ sb.patch) acc) q = FMap.get acc q := by
    induction slots generalizing acc with
    | nil => rfl
    | cons i rest ih =>
      rw [List.foldl_cons]
      cases hi : FMap.get w.sandbox i with
      | none => exact ih acc
      | some sb => rw [ih, FMap.get_merge_elim, absent i sb hi]; rfl
  exact fold _ ∅

theorem pending_sources (w : World sig) {q : sig.Path} {e : Edit sig}
    (get : FMap.get (pendingPatch w) q = some e) :
    ∃ i sb, FMap.get w.sandbox i = some sb ∧ FMap.get sb.patch q = some e := by
  classical
  have fold (slots : List Nat) (acc : Patch sig)
      (get : FMap.get (slots.foldl (fun acc i => match FMap.get w.sandbox i with
        | none => acc | some sb => acc ⊎ sb.patch) acc) q = some e) :
      FMap.get acc q = some e ∨
        ∃ i sb, FMap.get w.sandbox i = some sb ∧ FMap.get sb.patch q = some e := by
    induction slots generalizing acc with
    | nil => exact Or.inl get
    | cons i rest ih =>
      rw [List.foldl_cons] at get
      cases hi : FMap.get w.sandbox i with
      | none => exact ih acc (by simpa [hi] using get)
      | some sb =>
        rw [hi] at get
        rcases ih _ get with hp | found
        · rw [FMap.get_merge_elim] at hp
          cases hs : FMap.get sb.patch q with
          | none => exact Or.inl (by simpa [hs] using hp)
          | some v => exact Or.inr ⟨i, sb, hi, by simpa [hs] using hp⟩
        · exact Or.inr found
  exact (fold _ ∅ get).resolve_left (by simp [FMap.get])

theorem pending_some_iff (w : World sig) (disjoint : PendingDisjoint w)
    (q : sig.Path) (e : Edit sig) :
    FMap.get (pendingPatch w) q = some e ↔
      ∃ i sb, FMap.get w.sandbox i = some sb ∧ FMap.get sb.patch q = some e := by
  classical
  constructor
  · exact pending_sources w
  · rintro ⟨i, sb, hi, hp⟩
    rw [C8Steps.pending_lookup w i sb hi q]
    · exact hp
    · intro j other different hj hq
      apply Set.disjoint_left.mp (disjoint i j sb other different.symm hi hj) _ hq
      exact Finmap.mem_keys.mpr (Finmap.mem_iff.mpr ⟨e, hp⟩)

theorem disjoint_erase (w : World sig) (i : Nat) (old : PendingDisjoint w) :
    PendingDisjoint {w with sandbox := w.sandbox ∖ i} := by
  intro j k sb other different hj hk
  have ne {j : Nat} {sb : Sandbox sig}
      (get : FMap.get (w.sandbox ∖ i) j = some sb) : j ≠ i := by
    intro eq; subst j; simp [FMap.get_erase_self] at get
  exact old j k sb other different
    (by simpa only [FMap.get_erase_of_ne (ne hj)] using hj)
    (by simpa only [FMap.get_erase_of_ne (ne hk)] using hk)

theorem pending_factor (w : World sig) (i : Nat) (sb : Sandbox sig)
    (hi : FMap.get w.sandbox i = some sb) (old : PendingDisjoint w) :
    pendingPatch w = pendingPatch {w with sandbox := w.sandbox ∖ i} ⊎ sb.patch := by
  classical
  let rest := {w with sandbox := w.sandbox ∖ i}
  have rd := disjoint_erase w i old
  apply Finmap.ext_lookup
  intro q
  change FMap.get _ q = FMap.get _ q
  rw [FMap.get_merge_elim]
  cases hp : FMap.get sb.patch q with
  | some e =>
    simp only [Option.elim_some]
    apply (pending_some_iff w old q e).mpr
    exact ⟨i, sb, hi, hp⟩
  | none =>
    simp only [Option.elim_none]
    apply Option.ext
    intro e
    rw [pending_some_iff w old, pending_some_iff rest rd]
    constructor
    · rintro ⟨j, other, hj, hq⟩
      have ne : j ≠ i := by
        intro eq; subst j
        have eq := Option.some.inj (hi.symm.trans hj)
        subst other
        rw [hp] at hq
        contradiction
      exact ⟨j, other, by simpa only [rest, FMap.get_erase_of_ne ne] using hj, hq⟩
    · rintro ⟨j, other, hj, hq⟩
      have ne : j ≠ i := by
        intro eq; subst j
        simp [rest, FMap.get_erase_self] at hj
      exact ⟨j, other, by simpa only [rest, FMap.get_erase_of_ne ne] using hj, hq⟩

theorem disjoint_replace (w : World sig) (i : Nat) (sb : Sandbox sig)
    (old : PendingDisjoint w)
    (separated : ∀ j other, j ≠ i → FMap.get w.sandbox j = some other →
      Disjoint (FMap.dom sb.patch) (FMap.dom other.patch)) :
    PendingDisjoint {w with sandbox := w.sandbox[i ↦ sb]} := by
  classical
  intro j k a b ne hj hk
  by_cases hji : j = i
  · subst j
    have eq : a = sb := Option.some.inj (hj.symm.trans FMap.get_set_self)
    subst a
    rw [FMap.get_set_other ne.symm] at hk
    exact separated k b ne.symm hk
  · rw [FMap.get_set_other hji] at hj
    by_cases hki : k = i
    · subst k
      have eq : b = sb := Option.some.inj (hk.symm.trans FMap.get_set_self)
      subst b
      exact (separated j a hji hj).symm
    · rw [FMap.get_set_other hki] at hk
      exact old j k a b ne hj hk

theorem pending_replace (w : World sig) (i : Nat) (sb : Sandbox sig)
    (old : PendingDisjoint w)
    (separated : ∀ j other, j ≠ i → FMap.get w.sandbox j = some other →
      Disjoint (FMap.dom sb.patch) (FMap.dom other.patch)) :
    pendingPatch {w with sandbox := w.sandbox[i ↦ sb]} =
      pendingPatch {w with sandbox := w.sandbox ∖ i} ⊎ sb.patch := by
  classical
  rw [pending_factor _ i sb FMap.get_set_self (disjoint_replace w i sb old separated)]
  have maps : (w.sandbox[i ↦ sb]) ∖ i = w.sandbox ∖ i := by
    apply Finmap.ext_lookup
    intro j
    change FMap.get _ j = FMap.get _ j
    by_cases he : j = i
    · subst j; rw [FMap.get_erase_self, FMap.get_erase_self]
    · rw [FMap.get_erase_of_ne he, FMap.get_erase_of_ne he, FMap.get_set_other he]
  simp only [pendingPatch, maps]

theorem merge_assoc (a b c : Patch sig) : (a ⊎ b) ⊎ c = a ⊎ (b ⊎ c) := by
  classical
  apply Finmap.ext_lookup
  intro q
  change FMap.get _ q = FMap.get _ q
  simp only [FMap.get_merge_elim]
  cases FMap.get c q <;> rfl

theorem approx_refl (d : Patch sig) : PatchApprox d d := ⟨rfl, fun _ _ => rfl⟩

theorem overlay_open (live vanilla : FS sig) (rest staged call actual : Patch sig)
    (overlay : FSApprox vanilla (applyPatch live (rest ⊎ staged)))
    (patch : PatchApprox actual call) :
    FSApprox (applyPatch vanilla actual) (applyPatch live (rest ⊎ (staged ⊎ call))) := by
  have result := (patch_algebra (sig := sig)).2.2.2.1 _ _ _ _ overlay patch
  rw [(patch_algebra (sig := sig)).1, merge_assoc] at result
  exact result

theorem overlay_close (live vanilla : FS sig) (rest staged call actual memo : Patch sig)
    (overlay : FSApprox vanilla (applyPatch live (rest ⊎ staged)))
    (patch : PatchApprox actual call) (replay : PatchApprox memo (staged ⊎ call))
    (separated : Disjoint (FMap.dom rest) (FMap.dom (staged ⊎ call))) :
    FSApprox (applyPatch vanilla actual) (applyPatch (applyPatch live memo) rest) := by
  have left := overlay_open live vanilla rest staged call actual overlay patch
  have commute := (patch_algebra (sig := sig)).2.2.1 live rest (staged ⊎ call) separated
  rw [← (patch_algebra (sig := sig)).1, commute] at left
  have right := (patch_algebra (sig := sig)).2.2.2.1 live live memo (staged ⊎ call)
    (FSApprox.of_contents (fun _ => rfl)) replay
  have right' := (patch_algebra (sig := sig)).2.2.2.1 _ _ rest rest right (approx_refl rest)
  apply FSApprox.of_contents
  intro q
  exact (left.contents q).trans (right'.contents q).symm

theorem overlay_standalone (live vanilla : FS sig) (call actual : Patch sig)
    (overlay : FSApprox vanilla live) (patch : PatchApprox actual call) :
    FSApprox (applyPatch vanilla actual) (applyPatch live call) :=
  (patch_algebra (sig := sig)).2.2.2.1 _ _ _ _ overlay patch

theorem pending_disjoint_patch (w : World sig) (patch : Patch sig)
    (separated : ∀ i sb, FMap.get w.sandbox i = some sb →
      Disjoint (FMap.dom sb.patch) (FMap.dom patch)) :
    Disjoint (FMap.dom (pendingPatch w)) (FMap.dom patch) := by
  classical
  apply Set.disjoint_left.mpr
  intro q hq hp
  obtain ⟨e, he⟩ := Finmap.mem_iff.mp (Finmap.mem_keys.mp hq)
  obtain ⟨i, sb, hs, get⟩ := pending_sources w he
  exact Set.disjoint_left.mp (separated i sb hs)
    (Finmap.mem_keys.mpr (Finmap.mem_iff.mpr ⟨e, get⟩)) hp

theorem remaining_disjoint (w : World sig) (i : Nat) (sb : Sandbox sig)
    (hi : FMap.get w.sandbox i = some sb) (old : PendingDisjoint w)
    (call : Patch sig)
    (separated : ∀ j other, j ≠ i → FMap.get w.sandbox j = some other →
      Disjoint (FMap.dom call) (FMap.dom other.patch)) :
    Disjoint (FMap.dom (pendingPatch {w with sandbox := w.sandbox ∖ i}))
      (FMap.dom (sb.patch ⊎ call)) := by
  apply pending_disjoint_patch
  intro j other hj
  have ne : j ≠ i := by
    intro eq; subst j; simp [FMap.get_erase_self] at hj
  have get : FMap.get w.sandbox j = some other := by
    simpa only [FMap.get_erase_of_ne ne] using hj
  rw [FMap.dom_merge]
  exact Set.disjoint_union_right.mpr
    ⟨old j i other sb ne get hi, (separated j other ne get).symm⟩

theorem post_open (w : World sig) (vanilla : FS sig) (i : Nat) (sb : Sandbox sig)
    (hi : FMap.get w.sandbox i = some sb) (old : PendingDisjoint w)
    (input : Chunk) (r : Result sig) (hin : sb.input.flag = .open)
    (hout : sb.output.flag = .open) (actual : Patch sig)
    (overlay : FSApprox vanilla (applyPatch w.fs (pendingPatch w)))
    (patch : PatchApprox actual r.patch)
    (separated : ∀ j other, j ≠ i → FMap.get w.sandbox j = some other →
      Disjoint (FMap.dom r.patch) (FMap.dom other.patch)) :
    FSApprox (applyPatch vanilla actual)
      (applyPatch w.fs (pendingPatch
        {w with sandbox := w.sandbox[i ↦ (sb.accumulate input r hin hout)]})) := by
  have sep : ∀ j other, j ≠ i → FMap.get w.sandbox j = some other →
      Disjoint (FMap.dom (sb.accumulate input r hin hout).patch) (FMap.dom other.patch) := by
    intro j other ne get
    change Disjoint (FMap.dom (sb.patch ⊎ r.patch)) _
    rw [FMap.dom_merge]
    exact Set.disjoint_union_left.mpr ⟨old i j sb other ne.symm hi get, separated j other ne get⟩
  rw [pending_replace w i _ old sep]
  rw [pending_factor w i sb hi old] at overlay
  exact overlay_open _ _ _ _ _ _ overlay patch

theorem post_close (w : World sig) (vanilla : FS sig) (i : Nat) (sb : Sandbox sig)
    (hi : FMap.get w.sandbox i = some sb) (old : PendingDisjoint w)
    (call actual memo : Patch sig)
    (overlay : FSApprox vanilla (applyPatch w.fs (pendingPatch w)))
    (patch : PatchApprox actual call) (replay : PatchApprox memo (sb.patch ⊎ call))
    (separated : ∀ j other, j ≠ i → FMap.get w.sandbox j = some other →
      Disjoint (FMap.dom call) (FMap.dom other.patch)) :
    FSApprox (applyPatch vanilla actual)
      (applyPatch (applyPatch w.fs memo)
        (pendingPatch {w with sandbox := w.sandbox ∖ i})) := by
  rw [pending_factor w i sb hi old] at overlay
  exact overlay_close _ _ _ _ _ _ _ overlay patch replay
    (remaining_disjoint w i sb hi old call separated)

theorem merge_comm (a b : Patch sig) (disjoint : Disjoint (FMap.dom a) (FMap.dom b)) :
    a ⊎ b = b ⊎ a := by
  classical
  apply Finmap.ext_lookup
  intro q
  change FMap.get _ q = FMap.get _ q
  by_cases hq : q ∈ FMap.dom a
  · have hb := FMap.get_eq_none_of_disjoint disjoint.symm (fun _ h => h) hq
    simp only [FMap.get_merge_elim, hb, Option.elim_none]
    cases FMap.get a q <;> rfl
  · have ha : FMap.get a q = none :=
      FMap.get_eq_none.mpr (fun h => hq (Finmap.mem_keys.mpr h))
    simp only [FMap.get_merge_elim, ha, Option.elim_none]
    cases FMap.get b q <;> rfl

theorem pending_permutation (w : World sig) (old : PendingDisjoint w)
    (slots : List Nat) (order : slots.Perm (w.sandbox.keys.sort (· ≤ ·))) :
    slots.foldl (fun acc i => match FMap.get w.sandbox i with
      | none => acc | some sb => acc ⊎ sb.patch) ∅ = pendingPatch w := by
  classical
  let f := fun (acc : Patch sig) i => match FMap.get w.sandbox i with
    | none => acc | some sb => acc ⊎ sb.patch
  have comm : RightCommutative f := by
    constructor
    intro acc i j
    by_cases eq : i = j
    · subst j; rfl
    · dsimp [f]
      cases hi : FMap.get w.sandbox i <;> cases hj : FMap.get w.sandbox j
      · rfl
      · rfl
      · rfl
      · rename_i a b
        change (acc ⊎ a.patch) ⊎ b.patch = (acc ⊎ b.patch) ⊎ a.patch
        rw [merge_assoc, merge_assoc, merge_comm a.patch b.patch (old i j a b eq hi hj)]
  let := comm
  exact order.foldl_eq ∅

theorem standalone_pending {executor : Executor} {trace : Trace m h executor prog}
    {before selected : World sig} {selection : Selection sig} {p : sig.Probe}
    (discipline : SelectionDiscipline trace before selection selected)
    (head : selection.head = .standalone p) :
    pendingPatch before = ∅ ∧ pendingPatch selected = ∅ := by
  have law := discipline.2.2.2.2
  rw [head] at law
  constructor
  · apply C8Steps.pending_zero
    intro i sb get
    simp [law.2.2.1, FMap.get] at get
  · apply C8Steps.pending_zero
    intro i sb get
    simp [law.2.2.2.2.1, FMap.get] at get

theorem disjoint_accumulate (w : World sig) (i : Nat) (sb : Sandbox sig)
    (hi : FMap.get w.sandbox i = some sb) (old : PendingDisjoint w)
    (input : Chunk) (r : Result sig) (hin : sb.input.flag = .open)
    (hout : sb.output.flag = .open)
    (separated : ∀ j other, j ≠ i → FMap.get w.sandbox j = some other →
      Disjoint (FMap.dom r.patch) (FMap.dom other.patch)) :
    PendingDisjoint {w with sandbox := w.sandbox[i ↦ (sb.accumulate input r hin hout)]} := by
  apply disjoint_replace w i _ old
  intro j other ne get
  change Disjoint (FMap.dom (sb.patch ⊎ r.patch)) _
  rw [FMap.dom_merge]
  exact Set.disjoint_union_left.mpr
    ⟨old i j sb other ne.symm hi get, separated j other ne get⟩

theorem source_separation {executor : Executor} {trace : Trace m h executor prog}
    (isolated : Isolated trace) (entry i : Nat) (call : Patch sig) (w : World sig)
    (writes : FMap.dom call ⊆ componentWrites trace (.pipeline entry i))
    (otherWrites : ∀ j other, j ≠ i → FMap.get w.sandbox j = some other →
      FMap.dom other.patch ⊆ componentWrites trace (.pipeline entry j)) :
    ∀ j other, j ≠ i → FMap.get w.sandbox j = some other →
      Disjoint (FMap.dom call) (FMap.dom other.patch) := by
  intro j other ne get
  exact (isolated entry i j ne.symm).mono writes
    ((otherWrites j other ne get).trans Set.subset_union_right)

end
end Incr.Incr.OverlayUpdates


