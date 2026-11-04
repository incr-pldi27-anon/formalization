import Incr.IncrPP.Preservation.ProtectedIntervals

/-!
# Stability under a foreign recorded extension

The extension is an actual connected and operational step. A surviving
component retains its old first access and is still unclosed after a foreign
step. The protected-interval theorem then frames its accessed paths.
-/

namespace Incr.IncrPP

noncomputable section

variable {sig : Signature} {m : CommandModel sig} {h : Host sig}
  {executor : Executor} {prog : sig.Prog} {start : World sig}

/-- A foreign ordered extension preserves every previously accessed path of an unclosed component. -/
theorem Operational.foreign_extension_frame (host : HostWellFormed m h)
    (pre post : Prefix m h executor prog start) (postOperational : Operational post)
    (postOrdered : ExitOrdered post.trace) (d : StepDerivation m h executor prog)
    (joined : post.trace = pre.trace ++ [d]) (k : Component)
    (domain : k ∈ componentDomain pre.trace) (unclosed : closingPositions pre.trace k = [])
    (foreign : componentAt post.trace pre.trace.length d ≠ some k)
    (q : sig.Path) (accessed : q ∈ componentAccesses pre.trace k) :
    FMap.get d.after.fs q = FMap.get d.selected.fs q := by
  have atPos : (post.trace)[pre.trace.length]? = some d := by simp [joined]
  have domainPost : k ∈ componentDomain post.trace := by
    rw [joined]
    exact componentDomain_append_subset pre.trace [d] domain
  have accessedPost : q ∈ componentAccesses post.trace k := by
    rw [joined]
    exact componentAccesses_append_subset pre.trace [d] k accessed
  have first : firstAccess post.trace k q accessedPost = firstAccess pre.trace k q accessed := by
    simpa only [joined] using firstAccess_append pre.trace [d] k q accessed
  have firstBound : firstAccess post.trace k q accessedPost ≤ paperPosition pre.trace.length := by
    rw [first]
    exact Nat.le_trans (firstAccess_spec pre.trace k q accessed).2.2.1 (Nat.le_succ _)
  have noClose : closingPositions post.trace k = [] := by
    rw [joined, closingPositions_snoc]
    have different : componentAt (pre.trace ++ [d]) pre.trace.length d ≠ some k := by
      simpa [joined] using foreign
    simp [unclosed, different]
  have lastBound : paperPosition pre.trace.length ≤ lastPosition post.trace k := by
    unfold lastPosition
    rw [noClose]
    simp [joined, paperPosition]
  exact Operational.noForeignChanges host post postOperational postOrdered k domainPost q accessedPost
    pre.trace.length d atPos foreign firstBound lastBound

/-- An actual access belongs to an initialization already recorded in the trace. -/
theorem componentAccess_pipeline_entry_lt (trace : Trace m h executor prog) (entry slot : Nat)
    (q : sig.Path) (accessed : q ∈ componentAccesses trace (.pipeline entry slot)) :
    entry < trace.length := by
  have member := (firstAccess_spec trace (.pipeline entry slot) q accessed).1
  obtain ⟨pos, d, atPos, component, _, _⟩ := (mem_accessPositions_iff trace _ q _).mp member
  exact Nat.lt_of_le_of_lt (componentAt_pipeline_entry_le trace pos d component)
    (List.getElem?_eq_some_iff.mp atPos).choose

/-- The live entry's accumulated patch and dependency paths are stable under every ordered foreign step. -/
theorem Operational.live_foreign_extension (host : HostWellFormed m h)
    (pre post : Prefix m h .live prog start) (preOperational : Operational pre)
    (postOperational : Operational post) (postOrdered : ExitOrdered post.trace)
    (b : Boundary pre) (entry slot : Nat) (sb : Sandbox sig)
    (live : b.livePipeline entry slot) (present : FMap.get b.world.sandbox slot = some sb)
    (d : StepDerivation m h .live prog) (before : d.before = pre.final)
    (boundary : match b with
      | .final => True
      | .selected selection world _ => d.selection = selection ∧ d.selected = world)
    (joined : post.trace = pre.trace ++ [d])
    (foreign : componentAt post.trace pre.trace.length d ≠ some (.pipeline entry slot)) :
    ∀ q ∈ FMap.dom sb.patch ∪ FMap.dom sb.reads ∪ FMap.dom sb.writes,
      FMap.get d.after.fs q = FMap.get b.world.fs q := by
  intro q inEntry
  have fields := Operational.liveHistories host pre preOperational b entry slot sb live present
  have paths := (HistoryFields.component_paths pre.trace (.pipeline entry slot) sb fields).2
  have accessed : q ∈ componentAccesses pre.trace (.pipeline entry slot) := by
    rw [paths]
    exact inEntry
  have entryLt := componentAccess_pipeline_entry_lt pre.trace entry slot q accessed
  have domain : .pipeline entry slot ∈ componentDomain pre.trace := by
    cases b with
    | final => simpa [Boundary.componentDomain, Boundary.selection?] using live.2.1
    | selected selection world allowed =>
      exact Boundary.pipelineDomain_old pre selection world allowed entryLt live.2.1
  have frame := Operational.foreign_extension_frame host pre post postOperational postOrdered d joined
    (.pipeline entry slot) domain live.2.2 foreign q accessed
  have selectedFs : d.selected.fs = b.world.fs := by
    cases b with
    | final =>
      have allowed : h.select prog pre.final d.selection d.selected := by simpa [before] using d.host
      have discipline := host.selectionDiscipline .live prog start pre preOperational d.selection d.selected allowed
      simpa [Boundary.world] using discipline.1
    | selected selection world allowed =>
      simpa [Boundary.world] using congrArg World.fs boundary.2
  simpa [selectedFs] using frame

/-- Absorption survives any filesystem update that preserves the patch's paths. -/
theorem applyPatch_absorbed_of_frame (original current : FS sig) (patch : Patch sig)
    (absorbed : applyPatch original patch = original)
    (frame : ∀ q ∈ FMap.dom patch, FMap.get current q = FMap.get original q) :
    applyPatch current patch = current := by
  apply Finmap.ext_lookup
  intro q
  change FMap.get (applyPatch current patch) q = FMap.get current q
  cases lookup : FMap.get patch q with
  | none => exact applyPatch_get_none lookup
  | some edit =>
    have member : q ∈ FMap.dom patch := Finmap.mem_keys.mpr (Finmap.mem_iff.mpr ⟨edit, lookup⟩)
    have same := frame q member
    have initial := congrArg (fun fs => FMap.get fs q) absorbed
    cases edit with
    | delete => rw [applyPatch_get_delete lookup] at initial ⊢; exact initial.trans same.symm
    | write file => rw [applyPatch_get_write lookup] at initial ⊢; exact initial.trans same.symm

/-- Every live open judgment applies its retained result patch. -/
theorem LiveDerivation.open_fs {before after : World sig} {head : Head sig}
    {returned : Option Chunk} (d : LiveDerivation m before head after returned)
    (openInput : (LiveDerivation.input d).flag = .open) :
    after.fs = applyPatch before.fs (LiveDerivation.result d).patch := by
  cases d <;> simp_all [LiveDerivation.input, LiveDerivation.result]

/-- Each allocated live entry's accumulated patch is already reflected in the current filesystem. -/
def LiveAbsorbed (pre : Prefix m h .live prog start) (b : Boundary pre) : Prop :=
  ∀ entry slot sb, b.livePipeline entry slot → FMap.get b.world.sandbox slot = some sb →
    applyPatch b.world.fs sb.patch = b.world.fs

/-- A permitted selection preserves absorption, including freshly initialized entries. -/
theorem LiveAbsorbed.selected (pre : Prefix m h .live prog start)
    (absorbed : LiveAbsorbed pre .final) (selection : Selection sig) (world : World sig)
    (allowed : h.select prog pre.final selection world)
    (discipline : SelectionDiscipline pre.trace pre.final selection world) :
    LiveAbsorbed pre (.selected selection world allowed) := by
  intro entry slot sb live present
  rcases discipline with ⟨fsEq, _, _, allocation, _⟩
  cases initializes : selection.init with
  | none =>
    simp only [initializes] at allocation
    have oldLive : (Boundary.final : Boundary pre).livePipeline entry slot := by
      simpa [Boundary.livePipeline, Boundary.currentEntry, Boundary.componentDomain,
        Boundary.selection?, initializes] using live
    have old : FMap.get pre.final.sandbox slot = some sb := by
      simpa only [Boundary.world, allocation.1] using present
    simpa only [Boundary.world, fsEq] using absorbed entry slot sb oldLive old
  | some init =>
    simp only [initializes] at allocation
    have initial : sb = Sandbox.initial pre.final.fs := by
      apply initialSandboxes_value init pre.final.fs
      simpa only [Boundary.world, allocation.2.2.2.2] using present
    subst sb
    simpa [Boundary.world, Sandbox.initial] using applyPatch_empty world.fs

/-- Own opens update the absorbed patch; ordered foreign steps frame its existing keys. -/
theorem LiveAbsorbed.after_step (host : HostWellFormed m h)
    (pre post : Prefix m h .live prog start) (preOperational : Operational pre)
    (postOperational : Operational post) (postOrdered : ExitOrdered post.trace)
    (d : StepDerivation m h .live prog) (allowed : h.select prog pre.final d.selection d.selected)
    (joined : post.trace = pre.trace ++ [d]) (before : d.before = pre.final) (after : post.final = d.after)
    (absorbed : LiveAbsorbed pre (.selected d.selection d.selected allowed)) : LiveAbsorbed post .final := by
  intro entry slot sb live present
  have oldLive := ((Boundary.livePipeline_after_step pre post d allowed joined entry slot).mp live).1
  have actual : FMap.get d.after.sandbox slot = some sb := by
    simpa only [Boundary.world, after] using present
  rcases LiveDerivation.history_effect d.probe actual with own | foreign
  · obtain ⟨p, head, openInput, old, hin, hout, prior, rfl⟩ := own
    have oldAbsorbed := absorbed entry slot old oldLive prior
    have fsEffect := d.probe.open_fs openInput
    change applyPatch post.final.fs (old.patch ⊎ (LiveDerivation.result d.probe).patch) = post.final.fs
    rw [after, fsEffect]
    exact applyPatch_merge_absorbed d.selected.fs old.patch (LiveDerivation.result d.probe).patch oldAbsorbed
  · obtain ⟨prior, foreignHead⟩ := foreign
    have notSelected : componentAt post.trace pre.trace.length d ≠ some (.pipeline entry slot) := by
      intro selected
      rw [joined] at selected
      obtain ⟨p, head⟩ := componentAt_pipeline_head _ _ _ selected
      exact foreignHead p head
    have frame := Operational.live_foreign_extension host pre post preOperational postOperational postOrdered
      (.selected d.selection d.selected allowed) entry slot sb oldLive prior d before ⟨rfl, rfl⟩ joined notSelected
    change applyPatch post.final.fs sb.patch = post.final.fs
    rw [after]
    apply applyPatch_absorbed_of_frame d.selected.fs d.after.fs sb.patch
      (absorbed entry slot sb oldLive prior)
    intro q inPatch
    exact frame q (Or.inl (Or.inl inPatch))

/-- Ordered operational live endpoints absorb every live accumulated patch. -/
theorem Operational.liveAbsorbed_final (host : HostWellFormed m h)
    (pre : Prefix m h .live prog start) (operational : Operational pre) (ordered : ExitOrdered pre.trace) :
    LiveAbsorbed pre .final := by
  apply Operational.snoc_induction (fun pre => ExitOrdered pre.trace → LiveAbsorbed pre .final)
    ?_ ?_ pre operational ordered
  · intro pre _ empty _ entry slot sb _ present
    have connected := pre.connected
    rw [empty] at connected
    have endpoint := (Connected.nil_iff start pre.final).mp connected
    simp [Boundary.world, endpoint, pre.initial.2.1, FMap.get] at present
  · intro short post d shortOperational postOperational joined before after ih postOrdered
    have shortOrdered : ExitOrdered short.trace := by
      apply ExitOrdered.of_append short.trace [d]
      simpa only [joined] using postOrdered
    have allowed : h.select prog short.final d.selection d.selected := by
      simpa only [before] using d.host
    have discipline := host.selectionDiscipline .live prog start short shortOperational
      d.selection d.selected allowed
    have selected := LiveAbsorbed.selected short (ih shortOrdered) d.selection d.selected allowed discipline
    exact LiveAbsorbed.after_step host short post shortOperational postOperational postOrdered d allowed
      joined before.symm after selected

/-- Absorption also holds after every permitted selection, without a future-step premise. -/
theorem Operational.liveAbsorbed (host : HostWellFormed m h)
    (pre : Prefix m h .live prog start) (operational : Operational pre) (ordered : ExitOrdered pre.trace)
    (b : Boundary pre) : LiveAbsorbed pre b := by
  have endpoint := Operational.liveAbsorbed_final host pre operational ordered
  cases b with
  | final => exact endpoint
  | selected selection world allowed =>
    exact LiveAbsorbed.selected pre endpoint selection world allowed
      (host.selectionDiscipline .live prog start pre operational selection world allowed)

end
end IncrPP
end Incr
