import Incr.IncrPP.Semantics.Components

/-!
# E.1: live host assumptions

H1/H2/H3/H5 retain their printed meanings over both live executors.
Selection congruence compares independent prefixes using direct filesystem
agreement. It has no staged overlay, disjointness, common-start, equal-length,
exit-order, or cache-witness-consistency premise.
-/

namespace Incr.IncrPP

noncomputable section

variable {sig : Signature}

/-- H1 initializes every buffer, not only the first selected slot. -/
def initialBuffers (init : PipelineInit sig) : FMap Nat Chunk :=
  (init.probes.mapIdx fun i _ =>
    (⟨i, if i = 0 then init.input else Chunk.emptyOpen⟩ : Sigma (fun _ : Nat => Chunk))).toFinmap

/-- The paper's six initialized fields use the current filesystem snapshot. -/
def initialSandboxes (init : PipelineInit sig) (fs : FS sig) : FMap Nat (Sandbox sig) :=
  (init.probes.mapIdx fun i _ =>
    (⟨i, Sandbox.initial fs⟩ : Sigma (fun _ : Nat => Sandbox sig))).toFinmap

/-- Assignment comes from initialization, before any component has to execute. -/
def assignedProbes {m : CommandModel sig} {h : Host sig} {executor : Executor} {prog : sig.Prog}
    (trace : Trace m h executor prog) (selection : Selection sig) : Option (List sig.Probe) :=
  match selection.init with
  | some init => some init.probes
  | none => (latestPipeline trace).map fun entry => entry.2.probes

/-- H1 frame, pipeline initialization, and selection discipline. -/
def SelectionDiscipline {m : CommandModel sig} {h : Host sig}
    {executor : Executor} {prog : sig.Prog} (trace : Trace m h executor prog)
    (before : World sig) (selection : Selection sig) (selected : World sig) : Prop :=
  selected.fs = before.fs ∧ selected.ec = before.ec ∧ selected.cache = before.cache ∧
  (match selection.init with
  | some init =>
    before.buffer = ∅ ∧ before.sandbox = ∅ ∧ init.probes ≠ [] ∧
    selected.buffer = initialBuffers init ∧ selected.sandbox = initialSandboxes init before.fs
  | none => selected.sandbox = before.sandbox ∧
    FMap.dom selected.buffer = FMap.dom before.buffer) ∧
  (match selection.head with
  | .standalone _ =>
    selection.init = none ∧ before.buffer = ∅ ∧ before.sandbox = ∅ ∧
    selected.buffer = ∅ ∧ selected.sandbox = ∅ ∧ selected.stdin.flag = .eof
  | .pipeline p i =>
    selected.stdin = before.stdin ∧ i ∈ FMap.dom selected.buffer ∧
    i ∈ FMap.dom selected.sandbox ∧
    ∃ probes, assignedProbes trace selection = some probes ∧ probes[i]? = some p)

/-- H2 fixes each component's first actual probe and environment. -/
def ComponentEnvironments {m : CommandModel sig} {h : Host sig}
    {executor : Executor} {prog : sig.Prog} (trace : Trace m h executor prog) : Prop :=
  ∀ k first, (componentSteps trace k).head? = some first →
    ∀ d, d ∈ componentSteps trace k →
      d.selection.head = first.selection.head ∧ d.selected.env = first.selected.env

/-- O1 also constrains a progressed component's selection without a future probe step. -/
def ComponentSelectionEnvironments {m : CommandModel sig} {h : Host sig}
    {executor : Executor} {prog : sig.Prog} (trace : Trace m h executor prog)
    (selection : Selection sig) (selected : World sig) : Prop :=
  ∀ p i entry previous, selection.init = none → selection.head = .pipeline p i →
    LivePipelineComponent trace entry i → liveComponent trace i = some (.pipeline entry i) →
    previous ∈ componentSteps trace (.pipeline entry i) → selected.env = previous.selected.env

/-- H3 supplies input only by initialization or appending to an existing open slot zero. -/
def InputDelivery (before : World sig) (selection : Selection sig) (selected : World sig) : Prop :=
  match selection.init with
  | some _ => selection.delivery = none
  | none =>
    match selection.delivery with
    | none => selected.buffer = before.buffer
    | some chunk =>
      ∃ s, FMap.get before.buffer 0 = some ⟨s, .open⟩ ∧
        selected.buffer = before.buffer[0 ↦ ⟨s ++ chunk.bytes, chunk.flag⟩]

/-- The printed pre-selection control and input fields. -/
def ControlAgree (left right : World sig) : Prop :=
  left.pc = right.pc ∧ left.ec = right.ec ∧ left.env = right.env ∧
    left.buffer = right.buffer ∧ left.stdin = right.stdin

/-- O3 compares occurrence and ordered probe assignments, not complete annotations. -/
def MatchingSelections (left right : Selection sig) (selected selected' : World sig) : Prop :=
  left.head = right.head ∧ left.init.map (·.probes) = right.init.map (·.probes) ∧
    selected.pc = selected'.pc ∧ selected.env = selected'.env ∧
    selected.buffer = selected'.buffer ∧ selected.stdin = selected'.stdin

/-- Every host selection must match, without requiring a probe extension. -/
def SelectionsTransport (h : Host sig) (prog : sig.Prog) (left right : World sig) : Prop :=
  ∀ selection selected, h.select prog left selection selected →
    ∃ selection' selected', h.select prog right selection' selected' ∧
      MatchingSelections selection selection' selected selected'

/-- Live invocation domains correspond by initialization position and slot. -/
def LiveComponentsCorrespond {m : CommandModel sig} {h : Host sig}
    {prog : sig.Prog} (live : Trace m h .live prog) (vanilla : Trace m h .vanilla prog) : Prop :=
  ∀ entry slot, LivePipelineComponent live entry slot ↔ LivePipelineComponent vanilla entry slot

/-- E.1 replaces pending-patch selection by direct filesystem congruence. -/
structure HostWellFormed (m : CommandModel sig) (h : Host sig) : Prop where
  selectionDiscipline : ∀ executor prog start (pre : Prefix m h executor prog start),
    Operational pre → ∀ selection selected, h.select prog pre.final selection selected →
      SelectionDiscipline pre.trace pre.final selection selected
  componentEnvironments : ∀ executor prog start (pre : Prefix m h executor prog start),
    Operational pre → ComponentEnvironments pre.trace
  componentSelectionEnvironments : ∀ executor prog start (pre : Prefix m h executor prog start),
    Operational pre → ∀ selection selected, h.select prog pre.final selection selected →
      ComponentSelectionEnvironments pre.trace selection selected
  inputDelivery : ∀ executor prog start (pre : Prefix m h executor prog start),
    Operational pre → ∀ selection selected, h.select prog pre.final selection selected →
      InputDelivery pre.final selection selected
  selectionCongruence : ∀ prog (liveStart vanillaStart : World sig)
      (live : Prefix m h .live prog liveStart) (vanilla : Prefix m h .vanilla prog vanillaStart),
    Operational live → Operational vanilla → LiveComponentsCorrespond live.trace vanilla.trace →
    ControlAgree live.final vanilla.final → FSApprox live.final.fs vanilla.final.fs →
      SelectionsTransport h prog live.final vanilla.final ∧
        SelectionsTransport h prog vanilla.final live.final
  completionEmpty : ∀ prog w, h.complete prog w → w.buffer = ∅ ∧ w.sandbox = ∅
  completionNoSelection : ∀ prog w, h.complete prog w →
    ∀ selection selected, ¬ h.select prog w selection selected
  completionInvariance : ∀ prog w w',
    w.buffer = ∅ → w.sandbox = ∅ → w'.buffer = ∅ → w'.sandbox = ∅ →
    w.pc = w'.pc → w.ec = w'.ec → w.env = w'.env → w.stdin = w'.stdin →
    FSApprox w.fs w'.fs → (h.complete prog w ↔ h.complete prog w')

end
end IncrPP
end Incr
