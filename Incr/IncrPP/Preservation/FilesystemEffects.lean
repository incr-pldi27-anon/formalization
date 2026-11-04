import Incr.IncrPP.Preservation.LiveHistory

/-!
# Filesystem effects of retained live and vanilla probe judgments

Only the actual result patch can change the selected filesystem. A hit
applies its replay patch, which has the same domain as the retained memo patch.
-/

namespace Incr.IncrPP

noncomputable section

variable {sig : Signature} {m : CommandModel sig} {executor : Executor}

/-- A probe preserves each path outside its retained result patch domain. -/
theorem ProbeDerivation.fs_frame {before after : World sig} {head : Head sig}
    {returned : Option Chunk} (d : ProbeDerivation m executor before head after returned)
    (q : sig.Path) (outside : q ∉ FMap.dom (ProbeDerivation.result d).patch) :
    FMap.get after.fs q = FMap.get before.fs q := by
  cases executor <;> cases d
  all_goals simp only [ProbeDerivation.result, LiveDerivation.result, VanillaDerivation.result,
    closeWorld, standaloneWorld] at outside ⊢
  all_goals first
    | exact applyPatch_get_none (FMap.get_eq_none.mpr (fun member => outside (Finmap.mem_keys.mpr member)))
    | apply applyPatch_get_none
      apply FMap.get_eq_none.mpr
      intro member
      apply outside
      rw [← show FMap.dom _ = FMap.dom _ from (by assumption : PatchApprox _ _).1]
      exact Finmap.mem_keys.mpr member

/-- Applying successive patches equals applying their right-biased merge. -/
theorem applyPatch_merge (fs : FS sig) (first last : Patch sig) :
    applyPatch (applyPatch fs first) last = applyPatch fs (first ⊎ last) := by
  apply Finmap.ext_lookup
  intro q
  change FMap.get (applyPatch (applyPatch fs first) last) q = FMap.get (applyPatch fs (first ⊎ last)) q
  cases hl : FMap.get last q with
  | some e =>
    have merged : FMap.get (first ⊎ last) q = some e := FMap.get_merge_of_mem first last q e hl
    cases e with
    | delete => rw [applyPatch_get_delete hl, applyPatch_get_delete merged]
    | write f => rw [applyPatch_get_write hl, applyPatch_get_write merged]
  | none =>
    rw [applyPatch_get_none hl]
    have merged := FMap.get_merge_of_not_mem first last q hl
    cases hf : FMap.get first q with
    | none =>
      rw [applyPatch_get_none hf, applyPatch_get_none (merged.trans hf)]
    | some e =>
      cases e with
      | delete => rw [applyPatch_get_delete hf, applyPatch_get_delete (merged.trans hf)]
      | write f => rw [applyPatch_get_write hf, applyPatch_get_write (merged.trans hf)]

/-- An own open step retains absorption when its new patch is accumulated. -/
theorem applyPatch_merge_absorbed (fs : FS sig) (first last : Patch sig)
    (absorbed : applyPatch fs first = fs) :
    applyPatch (applyPatch fs last) (first ⊎ last) = applyPatch fs last := by
  apply Finmap.ext_lookup
  intro q
  change FMap.get (applyPatch (applyPatch fs last) (first ⊎ last)) q =
    FMap.get (applyPatch fs last) q
  cases hl : FMap.get last q with
  | some e =>
    have merged : FMap.get (first ⊎ last) q = some e := FMap.get_merge_of_mem first last q e hl
    cases e with
    | delete => rw [applyPatch_get_delete merged, applyPatch_get_delete hl]
    | write f => rw [applyPatch_get_write merged, applyPatch_get_write hl]
  | none =>
    rw [applyPatch_get_none hl, ← applyPatch_merge, applyPatch_get_none hl]
    cases hf : FMap.get first q with
    | none => rw [applyPatch_get_none hf, applyPatch_get_none hl]
    | some e =>
      have eq := congrArg (fun w => FMap.get w q) absorbed
      cases e with
      | delete => rw [applyPatch_get_delete hf] at eq ⊢; exact eq
      | write f => rw [applyPatch_get_write hf] at eq ⊢; exact eq

end
end IncrPP
end Incr
