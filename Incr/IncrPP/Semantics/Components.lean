import Incr.IncrPP.Semantics.Execution

/-!
# Live component identities and path sets

`def:paper-isolated` (pipeline isolation) supplies the component domain used by
E.2. Internal invocation indices
are zero-based list positions. `paperPosition` maps each recorded position
to the paper's one-based positions. Initialized slots stay in the domain
when unstepped or closed. A hit contributes the whole memo maps.
-/

namespace Incr.IncrPP

noncomputable section

variable {sig : Signature}

/-- Invocation identity, not a reusable slot or a probe name. -/
inductive Component where
  | standalone (position : Nat)
  | pipeline (entry : Nat) (slot : Nat)
  deriving DecidableEq, Repr

/-- Explicit index map from recorded list positions to paper positions. -/
def paperPosition (position : Nat) : Nat := position + 1

/-- The paper invocation identifiers retain slots and use one-based positions. -/
def Component.paperIndex : Component → Component
  | .standalone position => .standalone (paperPosition position)
  | .pipeline entry slot => .pipeline (paperPosition entry) slot

variable {m : CommandModel sig} {h : Host sig} {executor : Executor} {prog : sig.Prog}

/-- Latest initialization, including an initialization at the current step. -/
def latestPipeline (trace : Trace m h executor prog) : Option (Nat × PipelineInit sig) :=
  ((trace.mapIdx fun pos d => d.selection.init.map fun init => (pos, init)).filterMap id).getLast?

/-- The complete domain retains every initialized slot and standalone invocation. -/
def componentDomain (trace : Trace m h executor prog) : Set Component :=
  { k | ∃ pos d, (trace)[pos]? = some d ∧
      ((∃ p, d.selection.head = .standalone p ∧ k = .standalone pos) ∨
        ∃ init slot, d.selection.init = some init ∧ slot < init.probes.length ∧
          k = .pipeline pos slot) }

/-- Pipeline steps before any entry have no artificial component identity. -/
def componentAt (trace : Trace m h executor prog) (pos : Nat)
    (d : StepDerivation m h executor prog) : Option Component :=
  match d.selection.head with
  | .standalone _ => some (.standalone pos)
  | .pipeline _ slot =>
    (latestPipeline (trace.take (pos + 1))).map fun entry => .pipeline entry.1 slot

/-- The current pipeline identity at a slot. Liveness is checked separately. -/
def liveComponent (trace : Trace m h executor prog) (slot : Nat) : Option Component :=
  (latestPipeline trace).map fun entry => .pipeline entry.1 slot

/-- Ordered retained derivations at the positions of a component. -/
def componentSteps (trace : Trace m h executor prog) (k : Component) : Trace m h executor prog :=
  (trace.mapIdx fun pos d => (componentAt trace pos d, d)).filterMap fun pair =>
    if pair.1 = some k then some pair.2 else none

/-- The paper's one-based step set J_k, retained as an ordered list. -/
def componentPositions (trace : Trace m h executor prog) (k : Component) : List Nat :=
  (trace.mapIdx fun pos d =>
    if componentAt trace pos d = some k then some (paperPosition pos) else none).filterMap id

/-- Deletes count as writes. Hits use the entire memo patch, not only replay bytes. -/
def componentWrites (trace : Trace m h executor prog) (k : Component) : Set sig.Path :=
  { q | ∃ d ∈ componentSteps trace k, q ∈ FMap.dom (ProbeDerivation.result d.probe).patch }

/-- Whole memo dependencies contribute on a hit. -/
def componentDeps (trace : Trace m h executor prog) (k : Component) : Set sig.Path :=
  { q | ∃ d ∈ componentSteps trace k,
      q ∈ FMap.dom (ProbeDerivation.result d.probe).reads ∪
        FMap.dom (ProbeDerivation.result d.probe).writes }

/-- Dependencies and effects are both accesses. -/
def componentAccesses (trace : Trace m h executor prog) (k : Component) : Set sig.Path :=
  componentDeps trace k ∪ componentWrites trace k

/-- Access paths at one recorded probe judgment. -/
def StepDerivation.accesses (d : StepDerivation m h executor prog) : Set sig.Path :=
  FMap.dom (ProbeDerivation.result d.probe).patch ∪
    FMap.dom (ProbeDerivation.result d.probe).reads ∪
    FMap.dom (ProbeDerivation.result d.probe).writes

/-- One-based positions at which this component accesses the specified path. -/
def accessPositions (trace : Trace m h executor prog) (k : Component) (q : sig.Path) : List Nat := by
  classical
  exact (trace.mapIdx fun pos d =>
    if componentAt trace pos d = some k ∧ q ∈ d.accesses then
      some (paperPosition pos) else none).filterMap id

/-- Closing judgments consume EOF. Under the host discipline a component closes once. -/
def closingPositions (trace : Trace m h executor prog) (k : Component) : List Nat :=
  (trace.mapIdx fun pos d =>
    if componentAt trace pos d = some k ∧ (ProbeDerivation.input d.probe).flag = .eof then
      some (paperPosition pos) else none).filterMap id

/-- A live pipeline component was initialized and has not closed. -/
def LivePipelineComponent (trace : Trace m h executor prog) (entry slot : Nat) : Prop :=
  .pipeline entry slot ∈ componentDomain trace ∧
    closingPositions trace (.pipeline entry slot) = []

end
end IncrPP
end Incr
