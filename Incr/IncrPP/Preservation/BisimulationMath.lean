import Incr.IncrPP.Reuse.Statements

/-!
# Mathematical transport for live step matching

These lemmas use only shared filesystem, patch, record, and command
mathematics. They do not import the Incr 1.0 operational model.
-/

namespace Incr.IncrPP

noncomputable section

variable {sig : Signature} {m : CommandModel sig}

/-- Restricting content-equivalent filesystems preserves content equivalence. -/
theorem fsApprox_restrict {fs target : FS sig} (agreement : FSApprox fs target) (paths : Set sig.Path) :
    FSApprox (fs ↾ paths) (target ↾ paths) := by
  classical
  apply FSApprox.of_contents
  intro q
  simp only [FMap.get_restrict]
  split
  · exact agreement.contents q
  · rfl

/-- Patch agreement gives the same observed deletion or write contents at every path. -/
theorem patchApprox_contents {patch other : Patch sig} (agreement : PatchApprox patch other)
    (q : sig.Path) :
    (FMap.get patch q).map editContent = (FMap.get other q).map editContent := by
  classical
  by_cases present : q ∈ FMap.dom patch
  · exact agreement.2 q present
  · have absentOther : q ∉ FMap.dom other := by rw [← agreement.1]; exact present
    have firstNone : FMap.get patch q = none :=
      FMap.get_eq_none.mpr (fun member => present (Finmap.mem_keys.mpr member))
    have secondNone : FMap.get other q = none :=
      FMap.get_eq_none.mpr (fun member => absentOther (Finmap.mem_keys.mpr member))
    rw [firstNone, secondNone]

/-- Content-equivalent patches remain equivalent in either direction. -/
theorem patchApprox_symm {patch other : Patch sig} (agreement : PatchApprox patch other) :
    PatchApprox other patch := by
  refine ⟨agreement.1.symm, ?_⟩
  intro q _
  exact (patchApprox_contents agreement q).symm

/-- Content-equivalent patches compose transitively. -/
theorem patchApprox_trans {a b c : Patch sig} (ab : PatchApprox a b) (bc : PatchApprox b c) :
    PatchApprox a c := by
  exact ⟨ab.1.trans bc.1, fun q _ => (patchApprox_contents ab q).trans (patchApprox_contents bc q)⟩

/-- Applying a patch has the printed write, delete, and absent lookup behavior. -/
theorem applyPatch_lookup (fs : FS sig) (patch : Patch sig) (q : sig.Path) :
    FMap.get (applyPatch fs patch) q = match FMap.get patch q with
      | none => FMap.get fs q
      | some (.write file) => some file
      | some .delete => none := by
  cases found : FMap.get patch q with
  | none => exact applyPatch_get_none found
  | some edit =>
    cases edit with
    | write file => exact applyPatch_get_write found
    | delete => exact applyPatch_get_delete found

/-- Content-equivalent patches applied to equivalent filesystems give equivalent filesystems. -/
theorem fsApprox_applyPatch {fs target : FS sig} {patch other : Patch sig}
    (agreement : FSApprox fs target) (patches : PatchApprox patch other) :
    FSApprox (applyPatch fs patch) (applyPatch target other) := by
  apply FSApprox.of_contents
  intro q
  have original := agreement.contents q
  simp only [applyPatch_lookup]
  cases found : FMap.get patch q with
  | none =>
    have otherNone := PointwisePatchApprox.none (patchApprox_contents patches) found
    simpa only [otherNone] using original
  | some edit =>
    cases edit with
    | write file =>
      obtain ⟨otherFile, otherFound, content⟩ := PointwisePatchApprox.write (patchApprox_contents patches) found
      simp only [otherFound, Option.map_some]
      exact congrArg some content.symm
    | delete =>
      have otherFound := PointwisePatchApprox.delete (patchApprox_contents patches) found
      simp only [otherFound]

/-- Transfer a call to an equivalent target and choose timestamps fresh for all supplied records. -/
theorem transport_call_fresh (commands : WellFormedCommands m)
    (p : sig.Probe) (input : Chunk) (fs target live : FS sig) (env : Env sig) (result : Result sig)
    (call : m.denotes p input fs env result) (agreement : FSApprox fs target) (records : Records sig) :
    ∃ other, m.denotes p input target env other ∧ other.status = result.status ∧
      other.output = result.output ∧ other.writes = result.writes ∧
      FMap.dom other.reads = FMap.dom result.reads ∧ PatchApprox other.patch result.patch ∧
      FreshPatch other.patch target live ∧
      (∀ q file, FMap.get other.patch q = some (.write file) →
        ∀ q' old, (q', old) ∈ records → file.mtime ≠ old.mtime) := by
  obtain ⟨patch, reads, transported, approx, domains, _⟩ :=
    commands.dependencies.transport p input fs env result call target
      (fsApprox_restrict agreement (FMap.dom result.reads ∪ FMap.dom result.writes))
  let all := records ++ (fsRecords target ++ fsRecords live)
  let used : Set sig.MTime := {t | t ∈ all.map (fun x => x.2.mtime)}
  have finite : used.Finite := List.finite_toSet _
  obtain ⟨freshPatch, freshApprox, fresh⟩ := commands.timestamps.fresh used finite patch
  have retimed := commands.timestamps.retimestamp p input target env
    {result with patch := patch, reads := reads} transported freshPatch freshApprox
  refine ⟨{result with patch := freshPatch, reads := reads}, retimed, rfl, rfl, rfl,
    domains, patchApprox_trans freshApprox approx, ?_, ?_⟩
  · intro q file found q' old oldFound same
    apply fresh q file found
    change file.mtime ∈ all.map (fun x => x.2.mtime)
    rw [same]
    apply List.mem_map.mpr
    refine ⟨(q', old), ?_, rfl⟩
    rcases oldFound with targetFound | liveFound
    · exact List.mem_append.mpr (Or.inr (List.mem_append_left _ (mem_fsRecords_of_get targetFound)))
    · exact List.mem_append.mpr (Or.inr (List.mem_append_right _ (mem_fsRecords_of_get liveFound)))
  · intro q file found q' old oldFound same
    apply fresh q file found
    change file.mtime ∈ all.map (fun x => x.2.mtime)
    rw [same]
    exact List.mem_map.mpr ⟨(q', old), List.mem_append_left _ oldFound, rfl⟩

end
end IncrPP
end Incr
