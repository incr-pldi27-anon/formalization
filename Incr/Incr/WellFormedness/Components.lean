import Incr.Incr.Semantics.Execution

/-!
# Components and isolation over the new trace (paper `def:paper-isolated`)

The global recorded trace is primary. Component histories are projections
indexed by standalone selection position or pipeline entry and slot.
A component with no steps has empty write and access sets.
-/

open Incr
namespace Incr.Incr

noncomputable section

variable {sig : Signature}

/-- An invocation identity, not merely a command name or reusable slot. -/
inductive Component where
  | standalone (position : Nat)
  | pipeline (entry : Nat) (slot : Nat)
  deriving DecidableEq, Repr

/-- The latest pipeline initialization in this trace. -/
def latestPipeline {m : CommandModel sig} {h : Host sig} {executor : Executor} {prog : sig.Prog}
    (trace : Trace m h executor prog) : Option (Nat × PipelineInit sig) :=
  ((trace.mapIdx fun pos d => d.selection.init.map fun init => (pos, init)).filterMap id).getLast?

/-- A pipeline step without an entry has no component identity. Host H1 rules
out that case in admitted executions. There is no artificial default entry. -/
def componentAt {m : CommandModel sig} {h : Host sig} {executor : Executor} {prog : sig.Prog}
    (trace : Trace m h executor prog) (pos : Nat) (d : StepDerivation m h executor prog) :
    Option Component :=
  match d.selection.head with
  | .standalone _ => some (.standalone pos)
  | .pipeline _ slot =>
    (latestPipeline (trace.take (pos + 1))).map fun entry => .pipeline entry.1 slot

/-- The current pipeline's component at a slot, if any pipeline entry exists. -/
def liveComponent {m : CommandModel sig} {h : Host sig} {executor : Executor} {prog : sig.Prog}
    (trace : Trace m h executor prog) (slot : Nat) : Option Component :=
  (latestPipeline trace).map fun entry => .pipeline entry.1 slot

/-- The ordered subsequence at the positions `J_k` of paper `def:paper-isolated`. -/
def componentSteps {m : CommandModel sig} {h : Host sig} {executor : Executor} {prog : sig.Prog}
    (trace : Trace m h executor prog) (k : Component) : Trace m h executor prog :=
  (trace.mapIdx fun pos d => (componentAt trace pos d, d)).filterMap fun pair =>
    if pair.1 = some k then some pair.2 else none

/-- Deletes and writes in executed results or whole replayed memo patches. -/
def componentWrites {m : CommandModel sig} {h : Host sig} {executor : Executor} {prog : sig.Prog}
    (trace : Trace m h executor prog) (k : Component) : Set sig.Path :=
  {q | ∃ d ∈ componentSteps trace k, q ∈ FMap.dom (ProbeDerivation.result d.probe).patch}

/-- Dependencies of the selected results, including whole memo dependencies on a hit. -/
def componentDeps {m : CommandModel sig} {h : Host sig} {executor : Executor} {prog : sig.Prog}
    (trace : Trace m h executor prog) (k : Component) : Set sig.Path :=
  {q | ∃ d ∈ componentSteps trace k,
    q ∈ FMap.dom (ProbeDerivation.result d.probe).reads ∪
      FMap.dom (ProbeDerivation.result d.probe).writes}

/-- Accesses include dependency paths and effect paths. -/
def componentAccesses {m : CommandModel sig} {h : Host sig} {executor : Executor} {prog : sig.Prog}
    (trace : Trace m h executor prog) (k : Component) : Set sig.Path :=
  componentDeps trace k ∪ componentWrites trace k

/-- `def:paper-isolated` (pipeline isolation): ordered component pairs exclude
write/read and write/write communication. Closed components remain in the
comparison. -/
def Isolated {m : CommandModel sig} {h : Host sig} {executor : Executor} {prog : sig.Prog}
    (trace : Trace m h executor prog) : Prop :=
  ∀ entry i j, i ≠ j →
    Disjoint (componentWrites trace (.pipeline entry i))
      (componentAccesses trace (.pipeline entry j))

/-- `def:paper-program-wf` (program well-formedness): operational terminating
runs of both executors satisfy isolation. It does not require every execution
to terminate. -/
def WellFormedProgram (m : CommandModel sig) (h : Host sig) (prog : sig.Prog)
    (start : World sig) : Prop :=
  ∀ executor (run : Run m h executor prog start),
    Operational run.toPrefix → Isolated run.trace

end

end Incr.Incr
