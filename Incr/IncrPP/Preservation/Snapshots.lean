import Incr.IncrPP.Preservation.ClosingOrder

/-!
# Captured entry snapshots for E.4

A surviving sandbox retains its actual initialization snapshot. Vanilla
steps retain the entire initial payload. Live open steps change only the
accumulated fields, not the captured base.
-/

namespace Incr.IncrPP

noncomputable section

/-- A surviving lookup after erasure already existed before the erasure. -/
theorem lookup_erase_origin {K V : Type} [DecidableEq K] {map : FMap K V} {removed key : K} {value : V}
    (lookup : FMap.get (map ∖ removed) key = some value) : FMap.get map key = some value := by
  by_cases same : key = removed
  · subst key
    simp only [FMap.get_erase_self] at lookup
    contradiction
  · rwa [FMap.get_erase_of_ne same] at lookup

/-- An updated lookup is either the new entry or an unchanged entry at another key. -/
theorem lookup_set_origin {K V : Type} [DecidableEq K] {map : FMap K V} {key slot : K} {value found : V}
    (lookup : FMap.get (map[key ↦ value]) slot = some found) :
    (slot = key ∧ found = value) ∨ (slot ≠ key ∧ FMap.get map slot = some found) := by
  by_cases same : slot = key
  · subst slot
    rw [FMap.get_set_self] at lookup
    exact Or.inl ⟨rfl, (Option.some.inj lookup).symm⟩
  · rw [FMap.get_set_other same] at lookup
    exact Or.inr ⟨same, lookup⟩

variable {sig : Signature} {m : CommandModel sig} {h : Host sig}
  {executor : Executor} {prog : sig.Prog} {start : World sig}

/-- Every initialized payload is exactly the six-field initial sandbox. -/
theorem initialSandboxes_value (init : PipelineInit sig) (fs : FS sig) {slot : Nat} {sb : Sandbox sig}
    (lookup : FMap.get (initialSandboxes init fs) slot = some sb) : sb = Sandbox.initial fs := by
  rw [FMap.get, initialSandboxes, Finmap.dlookup_list_toFinmap] at lookup
  have member := List.of_mem_dlookup lookup
  obtain ⟨pos, bound, equal⟩ := List.mem_mapIdx.mp member
  exact (congrArg (fun pair : Sigma (fun _ : Nat => Sandbox sig) => pair.2) equal).symm

/-- Without initialization, the selected current entry is unchanged. -/
theorem Boundary.currentEntry_selected_none (pre : Prefix m h executor prog start)
    (selection : Selection sig) (world : World sig) (allowed : h.select prog pre.final selection world)
    (noInit : selection.init = none) :
    (Boundary.selected selection world allowed).currentEntry = (Boundary.final : Boundary pre).currentEntry := by
  simp [Boundary.currentEntry, Boundary.selection?, noInit]

/-- Without initialization, every selected entry lookup retains its recorded data. -/
theorem Boundary.entry_selected_none (pre : Prefix m h executor prog start)
    (selection : Selection sig) (world : World sig) (allowed : h.select prog pre.final selection world)
    (noInit : selection.init = none) (entry : Nat) :
    (Boundary.selected selection world allowed).entry entry = (Boundary.final : Boundary pre).entry entry := by
  simp [Boundary.entry, Boundary.selection?, noInit]

/-- A recorded current entry has an actual initialization before the prefix end. -/
theorem latestPipeline_current_lt (trace : Trace m h executor prog) {entry : Nat}
    (current : (latestPipeline trace).map Prod.fst = some entry) : entry < trace.length := by
  obtain ⟨pair, latest, index⟩ := Option.map_eq_some_iff.mp current
  rcases pair with ⟨origin, init⟩
  dsimp at index
  subst entry
  exact latestPipeline_entry_lt trace latest

/-- Recording a step preserves its already selected current entry's exact snapshot data. -/
theorem Boundary.entry_after_step (pre post : Prefix m h executor prog start)
    (d : StepDerivation m h executor prog) (allowed : h.select prog pre.final d.selection d.selected)
    (joined : post.trace = pre.trace ++ [d]) (before : pre.final = d.before) {entry : Nat}
    (current : (Boundary.selected d.selection d.selected allowed).currentEntry = some entry) :
    (Boundary.final : Boundary post).entry entry =
      (Boundary.selected d.selection d.selected allowed).entry entry := by
  cases initializes : d.selection.init with
  | none =>
    have epoch : (latestPipeline pre.trace).map Prod.fst = some entry := by
      simpa [Boundary.currentEntry, Boundary.selection?, initializes] using current
    have bound := latestPipeline_current_lt pre.trace epoch
    have nextBound : entry < pre.trace.length + 1 := Nat.lt_trans bound (Nat.lt_succ_self _)
    simp [Boundary.entry, Nat.ne_of_lt bound, Nat.ne_of_lt nextBound,
      joined, List.getElem?_append_left bound]
  | some init =>
    have index : pre.trace.length = entry := by
      simpa [Boundary.currentEntry, Boundary.selection?, initializes] using current
    subst entry
    simp [Boundary.entry, Boundary.selection?, joined, initializes, ← before]

/-- Surviving payloads retain an actual predecessor, its base, and all fields in vanilla mode. -/
theorem ProbeDerivation.sandbox_ancestor {before after : World sig} {head : Head sig}
    {returned : Option Chunk} (d : ProbeDerivation m executor before head after returned)
    {slot : Nat} {sb : Sandbox sig} (present : FMap.get after.sandbox slot = some sb) :
    ∃ old, FMap.get before.sandbox slot = some old ∧ sb.base = old.base ∧
      (executor = .vanilla → sb = old) := by
  cases executor <;> cases d
  case live.pipelineOpen =>
    rcases lookup_set_origin present with ⟨rfl, rfl⟩ | ⟨_, oldLookup⟩
    · exact ⟨‹Sandbox sig›, by assumption, rfl, fun impossible => nomatch impossible⟩
    · exact ⟨sb, oldLookup, rfl, fun _ => rfl⟩
  all_goals first
    | exact ⟨sb, present, rfl, fun _ => rfl⟩
    | exact ⟨sb, lookup_erase_origin present, rfl, fun _ => rfl⟩

/-- Every stored payload belongs to the current actual initialization. -/
def CapturedEntries (pre : Prefix m h executor prog start) (b : Boundary pre) : Prop :=
  ∀ slot sb, FMap.get b.world.sandbox slot = some sb →
    ∃ entry fs init, b.currentEntry = some entry ∧ b.entry entry = some (fs, init) ∧
      sb.base = fs ∧ (executor = .vanilla → sb = Sandbox.initial fs)

/-- Selection either retains the captured payloads or initializes the printed six fields. -/
theorem CapturedEntries.selected (pre : Prefix m h executor prog start)
    (captured : CapturedEntries pre .final) (selection : Selection sig) (world : World sig)
    (allowed : h.select prog pre.final selection world)
    (discipline : SelectionDiscipline pre.trace pre.final selection world) :
    CapturedEntries pre (.selected selection world allowed) := by
  intro slot sb present
  rcases discipline with ⟨_, _, _, allocation, _⟩
  cases initializes : selection.init with
  | none =>
    simp only [initializes] at allocation
    have old : FMap.get pre.final.sandbox slot = some sb := by
      simpa only [Boundary.world, allocation.1] using present
    obtain ⟨entry, fs, init, current, stored, base, vanilla⟩ := captured slot sb old
    refine ⟨entry, fs, init, ?_, ?_, base, vanilla⟩
    · rwa [Boundary.currentEntry_selected_none pre selection world allowed initializes]
    · rwa [Boundary.entry_selected_none pre selection world allowed initializes]
  | some init =>
    simp only [initializes] at allocation
    have initial : sb = Sandbox.initial pre.final.fs := by
      apply initialSandboxes_value init pre.final.fs
      simpa only [Boundary.world, allocation.2.2.2.2] using present
    subst sb
    refine ⟨pre.trace.length, pre.final.fs, init, ?_, ?_, rfl, fun _ => rfl⟩
    · simp [Boundary.currentEntry, Boundary.selection?, initializes]
    · simp [Boundary.entry, Boundary.selection?, initializes]

/-- Actual probe steps preserve snapshot provenance and the complete vanilla payload. -/
theorem CapturedEntries.after_step (pre post : Prefix m h executor prog start)
    (d : StepDerivation m h executor prog) (allowed : h.select prog pre.final d.selection d.selected)
    (joined : post.trace = pre.trace ++ [d]) (before : pre.final = d.before) (after : post.final = d.after)
    (captured : CapturedEntries pre (.selected d.selection d.selected allowed)) : CapturedEntries post .final := by
  intro slot sb present
  have actual : FMap.get d.after.sandbox slot = some sb := by
    simpa only [Boundary.world, after] using present
  obtain ⟨old, prior, sameBase, sameVanilla⟩ := d.probe.sandbox_ancestor actual
  obtain ⟨entry, fs, init, current, stored, base, vanilla⟩ := captured slot old prior
  refine ⟨entry, fs, init, ?_, ?_, sameBase.trans base, ?_⟩
  · rwa [Boundary.currentEntry_after_step pre post d allowed joined]
  · rw [Boundary.entry_after_step pre post d allowed joined before current]
    exact stored
  · intro mode
    exact (sameVanilla mode).trans (vanilla mode)

/-- All actual operational endpoints retain their initialization snapshot provenance. -/
theorem Operational.capturedEntries_final (host : HostWellFormed m h)
    (pre : Prefix m h executor prog start) (operational : Operational pre) : CapturedEntries pre .final := by
  apply Operational.snoc_induction (fun pre => CapturedEntries pre .final) ?_ ?_ pre operational
  · intro pre _ empty slot sb present
    have connected := pre.connected
    rw [empty] at connected
    have endpoint := (Connected.nil_iff start pre.final).mp connected
    simp [Boundary.world, endpoint, pre.initial.2.1, FMap.get] at present
  · intro short post d shortOperational _ joined before after ih
    have allowed : h.select prog short.final d.selection d.selected := by
      simpa only [before] using d.host
    have discipline := host.selectionDiscipline executor prog start short shortOperational
      d.selection d.selected allowed
    exact CapturedEntries.after_step short post d allowed joined before after
      (CapturedEntries.selected short ih d.selection d.selected allowed discipline)

/-- Provenance also holds at every permitted selection, without a following probe. -/
theorem Operational.capturedEntries (host : HostWellFormed m h)
    (pre : Prefix m h executor prog start) (operational : Operational pre) (b : Boundary pre) :
    CapturedEntries pre b := by
  have endpoint := Operational.capturedEntries_final host pre operational
  cases b with
  | final => exact endpoint
  | selected selection world allowed =>
    exact CapturedEntries.selected pre endpoint selection world allowed
      (host.selectionDiscipline executor prog start pre operational selection world allowed)

/-- E.4's captured-base clause for every live entry at either boundary kind. -/
theorem Boundary.snapshots (host : HostWellFormed m h)
    (pre : Prefix m h executor prog start) (operational : Operational pre) (b : Boundary pre) :
    ∀ entry slot sb, b.livePipeline entry slot → FMap.get b.world.sandbox slot = some sb →
      ∃ fs init, b.entry entry = some (fs, init) ∧ sb.base = fs := by
  intro entry slot sb live present
  obtain ⟨owner, fs, init, current, stored, base, _⟩ :=
    Operational.capturedEntries host pre operational b slot sb present
  have equal : owner = entry := Option.some.inj (current.symm.trans live.1)
  subst owner
  exact ⟨fs, init, stored, base⟩

/-- E.4's vanilla-entry clause retains the whole initial sandbox, not only its base. -/
theorem Boundary.vanillaEntries (host : HostWellFormed m h)
    (pre : Prefix m h executor prog start) (operational : Operational pre) (b : Boundary pre) :
    executor = .vanilla → ∀ entry slot sb, b.livePipeline entry slot →
      FMap.get b.world.sandbox slot = some sb →
        ∃ fs init, b.entry entry = some (fs, init) ∧ sb = Sandbox.initial fs := by
  intro mode entry slot sb live present
  obtain ⟨owner, fs, init, current, stored, _, vanilla⟩ :=
    Operational.capturedEntries host pre operational b slot sb present
  have equal : owner = entry := Option.some.inj (current.symm.trans live.1)
  subst owner
  exact ⟨fs, init, stored, vanilla mode⟩

end
end IncrPP
end Incr
