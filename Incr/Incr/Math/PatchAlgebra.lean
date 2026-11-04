import Incr.Incr.Preservation.PatchAlgebra

/-! # Patch algebra (`lem:paper-overlay`) -/

open Incr
namespace Incr.Incr

private theorem patch_lookup {sig : Signature} (fs : FS sig) (d : Patch sig)
    (q : sig.Path) :
    FMap.get (applyPatch fs d) q =
      match FMap.get d q with
      | none => FMap.get fs q
      | some (.write f) => some f
      | some .delete => none := by
  cases hd : FMap.get d q with
  | none => exact Incr.applyPatch_get_none hd
  | some e =>
    cases e with
    | write f => exact Incr.applyPatch_get_write hd
    | delete => exact Incr.applyPatch_get_delete hd

private theorem patch_contents {sig : Signature} {d d' : Patch sig}
    (h : PatchApprox d d') (q : sig.Path) :
    (FMap.get d q).map editContent = (FMap.get d' q).map editContent := by
  classical
  by_cases hq : q ∈ FMap.dom d
  · exact h.2 q hq
  · have hq' : q ∉ FMap.dom d' := by rw [← h.1]; exact hq
    have hn : FMap.get d q = none :=
      FMap.get_eq_none.mpr (fun hm => hq (Finmap.mem_keys.mpr hm))
    have hn' : FMap.get d' q = none :=
      FMap.get_eq_none.mpr (fun hm => hq' (Finmap.mem_keys.mpr hm))
    rw [hn, hn']

private theorem patch_of_contents {sig : Signature} {d d' : Patch sig}
    (h : ∀ q, (FMap.get d q).map editContent =
      (FMap.get d' q).map editContent) : PatchApprox d d' :=
  ⟨Incr.PointwisePatchApprox.dom_eq h, fun q _ => h q⟩

/-- `lem:paper-overlay` (patch algebra): all six patch-algebra claims. -/
theorem patch_algebra {sig : Signature} : PatchAlgebra sig := by
  classical
  refine ⟨?_, Incr.applyPatch_empty, ?_, ?_, ?_, ?_⟩
  · intro fs d₁ d₂
    apply Finmap.ext_lookup
    intro q
    change FMap.get _ q = FMap.get _ q
    simp only [patch_lookup, FMap.get_merge_elim]
    cases h₂ : FMap.get d₂ q with
    | none => simp only [Option.elim_none]
    | some e => cases e <;> rfl
  · intro fs d₁ d₂ hdisj
    apply Finmap.ext_lookup
    intro q
    change FMap.get _ q = FMap.get _ q
    by_cases hq : q ∈ FMap.dom d₁
    · have hn : FMap.get d₂ q = none :=
        FMap.get_eq_none_of_disjoint hdisj.symm (fun _ h => h) hq
      simp only [patch_lookup, hn]
    · have hn : FMap.get d₁ q = none :=
        FMap.get_eq_none.mpr (fun hm => hq (Finmap.mem_keys.mpr hm))
      simp only [patch_lookup, hn]
  · intro fs fs' d d' hfs hd
    apply FSApprox.of_contents
    intro q
    have hf := hfs.contents q
    simp only [patch_lookup]
    cases he : FMap.get d q with
    | none =>
      have he' : FMap.get d' q = none := Incr.PointwisePatchApprox.none (patch_contents hd) he
      simpa only [he'] using hf
    | some e =>
      cases e with
      | write f =>
        obtain ⟨f', he', hc⟩ := Incr.PointwisePatchApprox.write (patch_contents hd) he
        simp only [he', Option.map_some]
        exact congrArg some hc.symm
      | delete =>
        have he' := Incr.PointwisePatchApprox.delete (patch_contents hd) he
        simp only [he']
  · intro d₁ d₁' d₂ d₂' h₁ h₂
    apply patch_of_contents
    intro q
    have hp₁ := patch_contents h₁ q
    cases he₂ : FMap.get d₂ q with
    | none =>
      have he₂' := Incr.PointwisePatchApprox.none (patch_contents h₂) he₂
      simpa only [FMap.get_merge_elim, he₂, he₂', Option.elim_none] using hp₁
    | some e =>
      have hp₂ := patch_contents h₂ q
      cases he₂' : FMap.get d₂' q with
      | none => simp only [he₂, he₂', Option.map_some, Option.map_none] at hp₂; contradiction
      | some e' =>
        simpa only [FMap.get_merge_elim, he₂, he₂', Option.elim_some] using hp₂
  · intro fs d q hq
    apply Incr.applyPatch_get_none
    exact FMap.get_eq_none.mpr (fun hm => hq (Finmap.mem_keys.mpr hm))

end Incr.Incr
