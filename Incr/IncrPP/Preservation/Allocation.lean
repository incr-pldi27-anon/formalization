import Incr.IncrPP.Preservation.BufferOrder
import Incr.IncrPP.Preservation.ComponentEpochs
import Incr.IncrPP.Preservation.SlotEffects

/-!
# Exact allocation and retirement for E.4

The allocation invariant relates actual map domains to initialized components
without a closing position. Retirement records that an older epoch cannot
retain an unclosed component after a new pipeline has initialized.
-/

namespace Incr.IncrPP

noncomputable section

/-- Indexed initialization allocates exactly the indices of the source list. -/
theorem indexedMap_domain {α V : Type} (items : List α) (value : Nat → α → V) :
    FMap.dom ((items.mapIdx fun i item => (⟨i, value i item⟩ : Sigma (fun _ : Nat => V))).toFinmap) =
      {i | i < items.length} := by
  ext i
  change i ∈ (items.mapIdx fun j item => (⟨j, value j item⟩ : Sigma (fun _ : Nat => V))).toFinmap ↔ _
  rw [Finmap.mem_list_toFinmap]
  constructor
  · rintro ⟨v, member⟩
    obtain ⟨pos, bound, equal⟩ := List.mem_mapIdx.mp member
    have index : pos = i := congrArg Sigma.fst equal
    exact index ▸ bound
  · intro bound
    exact ⟨value i (items)[i], List.mem_mapIdx.mpr ⟨i, bound, rfl⟩⟩

variable {sig : Signature} {m : CommandModel sig} {h : Host sig}
  {executor : Executor} {prog : sig.Prog} {start : World sig}

/-- Initialization creates every buffer in the ordered probe assignment. -/
theorem initialBuffers_domain (init : PipelineInit sig) :
    FMap.dom (initialBuffers init) = {i | i < init.probes.length} :=
  indexedMap_domain init.probes _

/-- Initialization creates every sandbox, including slots that have not executed. -/
theorem initialSandboxes_domain (init : PipelineInit sig) (fs : FS sig) :
    FMap.dom (initialSandboxes init fs) = {i | i < init.probes.length} :=
  indexedMap_domain init.probes _

/-- Without initialization, a selected boundary has the same current unclosed domain. -/
theorem Boundary.unclosedSlots_selected_none (pre : Prefix m h executor prog start)
    (selection : Selection sig) (world : World sig) (allowed : h.select prog pre.final selection world)
    (noInit : selection.init = none) :
    (Boundary.selected selection world allowed).unclosedSlots = (Boundary.final : Boundary pre).unclosedSlots := by
  ext i
  simp [Boundary.unclosedSlots, Boundary.livePipeline, Boundary.currentEntry,
    Boundary.componentDomain, Boundary.selection?, noInit]

/-- The recorded post-step epoch is the one already present at its selected boundary. -/
theorem Boundary.currentEntry_snoc (pre : Prefix m h executor prog start)
    (d : StepDerivation m h executor prog) (allowed : h.select prog pre.final d.selection d.selected) :
    (latestPipeline (pre.trace ++ [d])).map Prod.fst =
      (Boundary.selected d.selection d.selected allowed).currentEntry := by
  cases init : d.selection.init <;>
    simp [latestPipeline_snoc, Boundary.currentEntry, Boundary.selection?, init]

/-- Recording a selection does not alter its initialized pipeline-component domain. -/
theorem Boundary.pipelineDomain_snoc (pre : Prefix m h executor prog start)
    (d : StepDerivation m h executor prog) (allowed : h.select prog pre.final d.selection d.selected)
    (entry slot : Nat) :
    .pipeline entry slot ∈ Incr.IncrPP.componentDomain (pre.trace ++ [d]) ↔
      .pipeline entry slot ∈ (Boundary.selected d.selection d.selected allowed).componentDomain := by
  simp [componentDomain_snoc, Boundary.componentDomain, Boundary.selection?]

/-- Every pending initialized slot is unclosed, without requiring a future probe. -/
theorem Boundary.unclosedSlots_selected_init (pre : Prefix m h executor prog start)
    (selection : Selection sig) (world : World sig) (allowed : h.select prog pre.final selection world)
    {init : PipelineInit sig} (initializes : selection.init = some init) :
    (Boundary.selected selection world allowed).unclosedSlots = {i | i < init.probes.length} := by
  ext slot
  have notOld : .pipeline pre.trace.length slot ∉ Incr.IncrPP.componentDomain pre.trace := by
    intro member
    exact Nat.lt_irrefl _ (componentDomain_pipeline_entry_lt pre.trace member)
  simp [Boundary.unclosedSlots, Boundary.livePipeline, Boundary.currentEntry,
    Boundary.componentDomain, Boundary.selection?, initializes, notOld,
    closingPositions_fresh pre.trace pre.trace.length slot (Nat.le_refl _)]

/-- Exact current allocation together with closure of every retired invocation. -/
structure SlotAllocation (pre : Prefix m h executor prog start) (b : Boundary pre) : Prop where
  buffers : FMap.dom b.world.buffer = b.unclosedSlots
  sandboxes : FMap.dom b.world.sandbox = b.unclosedSlots
  retired : ∀ entry slot, .pipeline entry slot ∈ b.componentDomain →
    b.currentEntry ≠ some entry → closingPositions pre.trace (.pipeline entry slot) ≠ []

/-- Host selection preserves exact allocation and retires only closed older components. -/
theorem SlotAllocation.selected (pre : Prefix m h executor prog start)
    (allocation : SlotAllocation pre .final) (selection : Selection sig) (world : World sig)
    (allowed : h.select prog pre.final selection world)
    (discipline : SelectionDiscipline pre.trace pre.final selection world) :
    SlotAllocation pre (.selected selection world allowed) := by
  have buffersEq : FMap.dom pre.final.buffer = (Boundary.final : Boundary pre).unclosedSlots :=
    allocation.buffers
  have sandboxesEq : FMap.dom pre.final.sandbox = (Boundary.final : Boundary pre).unclosedSlots :=
    allocation.sandboxes
  rcases discipline with ⟨_, _, _, allocationLaw, _⟩
  cases initializes : selection.init with
  | none =>
    simp only [initializes] at allocationLaw
    refine ⟨?_, ?_, ?_⟩
    · change FMap.dom world.buffer = _
      rw [allocationLaw.2, buffersEq,
        Boundary.unclosedSlots_selected_none pre selection world allowed initializes]
    · change FMap.dom world.sandbox = _
      rw [allocationLaw.1, sandboxesEq,
        Boundary.unclosedSlots_selected_none pre selection world allowed initializes]
    · intro entry slot present retired
      apply allocation.retired entry slot
      · simpa [Boundary.componentDomain, Boundary.selection?, initializes] using present
      · simpa [Boundary.currentEntry, Boundary.selection?, initializes] using retired
  | some init =>
    simp only [initializes] at allocationLaw
    refine ⟨?_, ?_, ?_⟩
    · change FMap.dom world.buffer = _
      rw [allocationLaw.2.2.2.1, initialBuffers_domain,
        Boundary.unclosedSlots_selected_init pre selection world allowed initializes]
    · change FMap.dom world.sandbox = _
      rw [allocationLaw.2.2.2.2, initialSandboxes_domain,
        Boundary.unclosedSlots_selected_init pre selection world allowed initializes]
    · intro entry slot present retired unclosed
      have domain : .pipeline entry slot ∈ Incr.IncrPP.componentDomain pre.trace ∨
          (slot < init.probes.length ∧ entry = pre.trace.length) := by
        simpa [Boundary.componentDomain, Boundary.selection?, initializes] using present
      rcases domain with old | fresh
      · have oldDomain : .pipeline entry slot ∈ (Boundary.final : Boundary pre).componentDomain := by
          simpa [Boundary.componentDomain, Boundary.selection?] using old
        have current : (Boundary.final : Boundary pre).currentEntry = some entry := by
          by_contra notCurrent
          exact allocation.retired entry slot oldDomain notCurrent unclosed
        have allocated : slot ∈ FMap.dom pre.final.buffer := by
          rw [buffersEq]
          exact ⟨entry, current, oldDomain, unclosed⟩
        simp [allocationLaw.1] at allocated
      · apply retired
        simp [Boundary.currentEntry, Boundary.selection?, initializes, fresh.2]

/-- The current entry after recording a step equals its already selected entry. -/
theorem Boundary.currentEntry_after_step (pre post : Prefix m h executor prog start)
    (d : StepDerivation m h executor prog) (allowed : h.select prog pre.final d.selection d.selected)
    (joined : post.trace = pre.trace ++ [d]) :
    (Boundary.final : Boundary post).currentEntry =
      (Boundary.selected d.selection d.selected allowed).currentEntry := by
  change (latestPipeline post.trace).map Prod.fst = _
  rw [joined]
  exact Boundary.currentEntry_snoc pre d allowed

/-- Recording a step keeps precisely the selected pipeline-component domain. -/
theorem Boundary.pipelineDomain_after_step (pre post : Prefix m h executor prog start)
    (d : StepDerivation m h executor prog) (allowed : h.select prog pre.final d.selection d.selected)
    (joined : post.trace = pre.trace ++ [d]) (entry slot : Nat) :
    .pipeline entry slot ∈ (Boundary.final : Boundary post).componentDomain ↔
      .pipeline entry slot ∈ (Boundary.selected d.selection d.selected allowed).componentDomain := by
  simpa [Boundary.componentDomain, Boundary.selection?, joined] using
    Boundary.pipelineDomain_snoc pre d allowed entry slot

/-- A selected pipeline step uses the same current entry when it becomes recorded. -/
theorem Boundary.componentAt_selected (pre : Prefix m h executor prog start)
    (d : StepDerivation m h executor prog) (allowed : h.select prog pre.final d.selection d.selected)
    {p : sig.Probe} {slot : Nat} (head : d.selection.head = .pipeline p slot) :
    componentAt (pre.trace ++ [d]) pre.trace.length d =
      (Boundary.selected d.selection d.selected allowed).currentEntry.map fun entry => .pipeline entry slot := by
  rw [componentAt_snoc, head, latestPipeline_snoc]
  cases initializes : d.selection.init <;>
    simp [Boundary.currentEntry, Boundary.selection?, initializes, Option.map_map, Function.comp_def]

/-- A pipeline component remains live unless this exact step closes it. -/
theorem Boundary.livePipeline_after_step (pre post : Prefix m h executor prog start)
    (d : StepDerivation m h executor prog) (allowed : h.select prog pre.final d.selection d.selected)
    (joined : post.trace = pre.trace ++ [d]) (entry slot : Nat) :
    (Boundary.final : Boundary post).livePipeline entry slot ↔
      (Boundary.selected d.selection d.selected allowed).livePipeline entry slot ∧
        ¬ (componentAt (pre.trace ++ [d]) pre.trace.length d = some (.pipeline entry slot) ∧
          (ProbeDerivation.input d.probe).flag = .eof) := by
  unfold Boundary.livePipeline
  rw [Boundary.currentEntry_after_step pre post d allowed joined,
    Boundary.pipelineDomain_after_step pre post d allowed joined, joined, closingPositions_snoc]
  split <;> simp_all

/-- An EOF pipeline step removes exactly its own slot from the unclosed set. -/
theorem Boundary.unclosedSlots_pipeline_step (pre post : Prefix m h executor prog start)
    (d : StepDerivation m h executor prog) (allowed : h.select prog pre.final d.selection d.selected)
    (joined : post.trace = pre.trace ++ [d]) {p : sig.Probe} {slot entry : Nat}
    (head : d.selection.head = .pipeline p slot)
    (current : (Boundary.selected d.selection d.selected allowed).currentEntry = some entry) :
    (Boundary.final : Boundary post).unclosedSlots = if (ProbeDerivation.input d.probe).flag = .eof then
      {j | j ∈ (Boundary.selected d.selection d.selected allowed).unclosedSlots ∧ j ≠ slot}
      else (Boundary.selected d.selection d.selected allowed).unclosedSlots := by
  have selected : componentAt (pre.trace ++ [d]) pre.trace.length d = some (.pipeline entry slot) := by
    rw [Boundary.componentAt_selected pre d allowed head, current]
    rfl
  ext j
  by_cases eofFlag : (ProbeDerivation.input d.probe).flag = .eof
  · simp only [eofFlag, ite_true, Set.mem_ofPred_eq]
    change (∃ e, (Boundary.final : Boundary post).livePipeline e j) ↔ _
    simp only [Boundary.livePipeline_after_step pre post d allowed joined]
    simp [Boundary.unclosedSlots, Boundary.livePipeline, current, selected, eofFlag, and_assoc, ne_comm]
  · simp only [eofFlag, ite_false]
    change (∃ e, (Boundary.final : Boundary post).livePipeline e j) ↔ _
    simp only [Boundary.livePipeline_after_step pre post d allowed joined]
    simp [eofFlag, Boundary.unclosedSlots]

/-- Standalone steps close no pipeline component. -/
theorem Boundary.unclosedSlots_standalone_step (pre post : Prefix m h executor prog start)
    (d : StepDerivation m h executor prog) (allowed : h.select prog pre.final d.selection d.selected)
    (joined : post.trace = pre.trace ++ [d]) {p : sig.Probe} (head : d.selection.head = .standalone p) :
    (Boundary.final : Boundary post).unclosedSlots =
      (Boundary.selected d.selection d.selected allowed).unclosedSlots := by
  have selected : componentAt (pre.trace ++ [d]) pre.trace.length d = some (.standalone pre.trace.length) := by
    rw [componentAt_snoc, head]
  ext slot
  simp [Boundary.unclosedSlots, Boundary.livePipeline_after_step pre post d allowed joined, selected]

/-- A recorded probe cannot reopen any already retired component. -/
theorem SlotAllocation.retired_after_step (pre post : Prefix m h executor prog start)
    (d : StepDerivation m h executor prog) (allowed : h.select prog pre.final d.selection d.selected)
    (joined : post.trace = pre.trace ++ [d])
    (allocation : SlotAllocation pre (.selected d.selection d.selected allowed)) :
    ∀ entry slot, .pipeline entry slot ∈ (Boundary.final : Boundary post).componentDomain →
      (Boundary.final : Boundary post).currentEntry ≠ some entry →
        closingPositions post.trace (.pipeline entry slot) ≠ [] := by
  intro entry slot present retired unclosed
  have domain := (Boundary.pipelineDomain_after_step pre post d allowed joined entry slot).mp present
  have notCurrent : (Boundary.selected d.selection d.selected allowed).currentEntry ≠ some entry := by
    rwa [Boundary.currentEntry_after_step pre post d allowed joined] at retired
  have oldClosed := allocation.retired entry slot domain notCurrent
  rw [joined, closingPositions_snoc] at unclosed
  exact oldClosed (List.append_eq_nil_iff.mp unclosed).1

/-- Actual raw map effects agree with the recorded unclosed-component update. -/
theorem SlotAllocation.after_step (pre post : Prefix m h executor prog start)
    (d : StepDerivation m h executor prog) (allowed : h.select prog pre.final d.selection d.selected)
    (joined : post.trace = pre.trace ++ [d]) (after : post.final = d.after)
    (allocation : SlotAllocation pre (.selected d.selection d.selected allowed)) :
    SlotAllocation post .final := by
  have buffersEq : FMap.dom d.selected.buffer =
      (Boundary.selected d.selection d.selected allowed).unclosedSlots := allocation.buffers
  have sandboxesEq : FMap.dom d.selected.sandbox =
      (Boundary.selected d.selection d.selected allowed).unclosedSlots := allocation.sandboxes
  have domains : FMap.dom d.after.buffer = (Boundary.final : Boundary post).unclosedSlots ∧
      FMap.dom d.after.sandbox = (Boundary.final : Boundary post).unclosedSlots := by
    cases head : d.selection.head with
    | standalone p =>
      have framed := d.probe.slots_of_standalone head
      rw [Boundary.unclosedSlots_standalone_step pre post d allowed joined head, framed.1, framed.2]
      exact ⟨buffersEq, sandboxesEq⟩
    | pipeline p slot =>
      have present : slot ∈ FMap.dom d.selected.buffer := by
        have raw := d.probe
        rw [head] at raw
        exact raw.pipeline_buffer_present
      rw [buffersEq] at present
      obtain ⟨entry, current, _, _⟩ := present
      rw [Boundary.unclosedSlots_pipeline_step pre post d allowed joined head current]
      constructor
      · simpa only [buffersEq] using d.probe.buffers_domain head
      · simpa only [sandboxesEq] using d.probe.sandboxes_domain head
  refine ⟨?_, ?_, SlotAllocation.retired_after_step pre post d allowed joined allocation⟩
  · change FMap.dom post.final.buffer = _
    simpa only [after] using domains.1
  · change FMap.dom post.final.sandbox = _
    simpa only [after] using domains.2

/-- Operational prefixes allocate exactly their current unclosed components. -/
theorem Operational.slotAllocation_final (host : HostWellFormed m h)
    (pre : Prefix m h executor prog start) (operational : Operational pre) : SlotAllocation pre .final := by
  apply Operational.snoc_induction (fun pre => SlotAllocation pre .final) ?_ ?_ pre operational
  · intro pre _ empty
    have connected := pre.connected
    rw [empty] at connected
    have endpoint := (Connected.nil_iff start pre.final).mp connected
    have unclosed : (Boundary.final : Boundary pre).unclosedSlots = ∅ := by
      ext slot
      simp [Boundary.unclosedSlots, Boundary.livePipeline, Boundary.currentEntry,
        Boundary.selection?, empty, latestPipeline]
    refine ⟨?_, ?_, ?_⟩
    · simp only [Boundary.world, endpoint, pre.initial.1, FMap.dom_empty, unclosed]
    · simp only [Boundary.world, endpoint, pre.initial.2.1, FMap.dom_empty, unclosed]
    · intro entry slot present
      simp [Boundary.componentDomain, Boundary.selection?, empty, componentDomain] at present
  · intro short post d shortOperational _ joined before after ih
    have allowed : h.select prog short.final d.selection d.selected := by
      simpa only [before] using d.host
    have discipline := host.selectionDiscipline executor prog start short shortOperational
      d.selection d.selected allowed
    exact SlotAllocation.after_step short post d allowed joined after
      (SlotAllocation.selected short ih d.selection d.selected allowed discipline)

/-- The exact allocation and retirement invariant also holds after every permitted selection. -/
theorem Operational.slotAllocation (host : HostWellFormed m h)
    (pre : Prefix m h executor prog start) (operational : Operational pre) (b : Boundary pre) :
    SlotAllocation pre b := by
  have endpoint := Operational.slotAllocation_final host pre operational
  cases b with
  | final => exact endpoint
  | selected selection world allowed =>
    exact SlotAllocation.selected pre endpoint selection world allowed
      (host.selectionDiscipline executor prog start pre operational selection world allowed)

/-- E.4's exact buffer-domain clause, including initialized but unstepped slots. -/
theorem Boundary.buffers_domain (host : HostWellFormed m h)
    (pre : Prefix m h executor prog start) (operational : Operational pre) (b : Boundary pre) :
    FMap.dom b.world.buffer = b.unclosedSlots :=
  (Operational.slotAllocation host pre operational b).buffers

/-- E.4's exact sandbox-domain clause for both executors and both boundary kinds. -/
theorem Boundary.sandboxes_domain (host : HostWellFormed m h)
    (pre : Prefix m h executor prog start) (operational : Operational pre) (b : Boundary pre) :
    FMap.dom b.world.sandbox = b.unclosedSlots :=
  (Operational.slotAllocation host pre operational b).sandboxes

/-- A selected component has no earlier closing, including a fresh standalone invocation. -/
theorem StepDerivation.no_prior_close (pre : Prefix m h executor prog start)
    (d : StepDerivation m h executor prog) (allowed : h.select prog pre.final d.selection d.selected)
    (allocation : SlotAllocation pre (.selected d.selection d.selected allowed))
    (k : Component) (selected : componentAt (pre.trace ++ [d]) pre.trace.length d = some k) :
    closingPositions pre.trace k = [] := by
  cases head : d.selection.head with
  | standalone p =>
    have named : componentAt (pre.trace ++ [d]) pre.trace.length d = some (.standalone pre.trace.length) := by
      rw [componentAt_snoc, head]
    rw [named] at selected
    cases Option.some.inj selected
    exact closingPositions_standalone_fresh pre.trace pre.trace.length (Nat.le_refl _)
  | pipeline p slot =>
    have present : slot ∈ FMap.dom d.selected.buffer := by
      have raw := d.probe
      rw [head] at raw
      exact raw.pipeline_buffer_present
    have buffersEq : FMap.dom d.selected.buffer =
        (Boundary.selected d.selection d.selected allowed).unclosedSlots := allocation.buffers
    rw [buffersEq] at present
    obtain ⟨entry, current, _, unclosed⟩ := present
    have named : componentAt (pre.trace ++ [d]) pre.trace.length d = some (.pipeline entry slot) := by
      rw [Boundary.componentAt_selected pre d allowed head, current]
      rfl
    rw [named] at selected
    cases Option.some.inj selected
    exact unclosed

/-- Host-disciplined operational invocations have at most one closing judgment. -/
theorem Operational.closing_unique (host : HostWellFormed m h)
    (pre : Prefix m h executor prog start) (operational : Operational pre) :
    ∀ k, (closingPositions pre.trace k).length ≤ 1 := by
  apply Operational.snoc_induction
    (fun pre => ∀ k, (closingPositions pre.trace k).length ≤ 1) ?_ ?_ pre operational
  · intro pre _ empty k
    simp [empty, closingPositions]
  · intro short post d shortOperational _ joined before after ih k
    have allowed : h.select prog short.final d.selection d.selected := by
      simpa only [before] using d.host
    have allocation := Operational.slotAllocation host short shortOperational
      (.selected d.selection d.selected allowed)
    rw [joined, closingPositions_snoc]
    by_cases closes : componentAt (short.trace ++ [d]) short.trace.length d = some k ∧
        (ProbeDerivation.input d.probe).flag = .eof
    · have unclosed := StepDerivation.no_prior_close short d allowed allocation k closes.1
      simp [closes, unclosed]
    · simp only [closes, ite_false, List.append_nil]
      exact ih k

end
end IncrPP
end Incr
