import Incr.Incr.WellFormedness.Host
import Incr.Assumptions.Commands
import Incr.Incr.WellFormedness.Sandboxes

/-!
# Preservation statement vocabulary (paper `app:proof-preservation`)

Component histories are projections of recorded whole steps. Accumulation is
an explicit relation, so invalid chunk concatenations are not silently
skipped or assigned an arbitrary value. The numbered proofs are separate.
-/

open Incr
namespace Incr.Incr

noncomputable section

variable {sig : Signature} {m : CommandModel sig} {h : Host sig}
  {executor : Executor} {prog : sig.Prog} {start : World sig}

/-- The component's preceding open-input probe steps, in trace order. -/
def openHistory (trace : Trace m h executor prog) (k : Component) : Trace m h executor prog :=
  (componentSteps trace k).filter fun d => (ProbeDerivation.input d.probe).flag = .open

/-- An EOF-input probe step closes this pipeline invocation and slot. -/
def slotClosed (trace : Trace m h executor prog) (entry slot : Nat) : Prop :=
  ∃ d ∈ componentSteps trace (.pipeline entry slot),
    (ProbeDerivation.input d.probe).flag = .eof

/-- `lem:paper-buffers` clause (ii): the exact successive input/output and
restricted dependency merges.
This relation is defined only when each accumulated left chunk is open. -/
inductive HistoryAccumulation (base : FS sig) :
    Trace m h executor prog → Sandbox sig → Prop
  | nil : HistoryAccumulation base [] (Sandbox.initial base)
  | snoc (trace : Trace m h executor prog) (sb : Sandbox sig)
      (d : StepDerivation m h executor prog)
      (previous : HistoryAccumulation base trace sb)
      (hi : sb.input.flag = .open) (ho : sb.output.flag = .open)
      (hopen : (ProbeDerivation.input d.probe).flag = .open) :
      HistoryAccumulation base (trace ++ [d])
        (sb.accumulate (ProbeDerivation.input d.probe) (ProbeDerivation.result d.probe) hi ho)

/-- `lem:paper-buffers` clause (iii): a present slot's immediate successor,
when present, is open.
The live-slot clause below supplies successor presence when that slot exists. -/
def BufferOrder (buffers : FMap Nat Chunk) : Prop :=
  ∀ i b successor, FMap.get buffers i = some b →
    FMap.get buffers (i + 1) = some successor → successor.flag = .open

/-- `lem:paper-buffers` clause (iii): every lower slot has closed before a
higher slot closes. -/
def ClosingOrder (trace : Trace m h executor prog) : Prop :=
  ∀ pos d entry j, (trace)[pos]? = some d →
    componentAt trace pos d = some (.pipeline entry j) →
    (ProbeDerivation.input d.probe).flag = .eof →
    ∀ i, i < j → ∃ earlier previous,
      earlier < pos ∧ (trace)[earlier]? = some previous ∧
      componentAt trace earlier previous = some (.pipeline entry i) ∧
      (ProbeDerivation.input previous.probe).flag = .eof

/-- `lem:paper-buffers` clauses (i)--(iii): live domains, entry bases, exact
accumulated fields, and
open successors. The vanilla branch retains initialized sandbox fields. -/
def SandboxState (trace : Trace m h executor prog) (w : World sig) : Prop :=
  FMap.dom w.buffer = FMap.dom w.sandbox ∧
  (∀ i sb, FMap.get w.sandbox i = some sb →
    ∃ entry init entryStep,
      latestPipeline trace = some (entry, init) ∧ (trace)[entry]? = some entryStep ∧
      entryStep.selection.init = some init ∧ sb.base = entryStep.before.fs ∧
      (match executor with
      | .incr => HistoryAccumulation sb.base (openHistory trace (.pipeline entry i)) sb
      | .vanilla => sb = Sandbox.initial sb.base)) ∧
  BufferOrder w.buffer ∧
  (∀ entry init, latestPipeline trace = some (entry, init) →
    ∀ i, i ∈ FMap.dom w.sandbox ↔
      i < init.probes.length ∧ ¬ slotClosed trace entry i) ∧
  (latestPipeline trace = none → FMap.dom w.sandbox = ∅) ∧
  (∀ entry init, latestPipeline trace = some (entry, init) →
    ∀ i, i + 1 < init.probes.length →
      i ∈ FMap.dom w.sandbox → i + 1 ∈ FMap.dom w.sandbox) ∧
  ClosingOrder trace

/-- The `lem:paper-buffers` routing clause for actual recorded component steps.
The derivation supplies the concrete buffer map after source consumption.
No hypothetical buffer map occurs in the numbered conclusion. -/
def RoutingReady (trace : Trace m h executor prog) : Prop :=
  ∀ pos d p i, (trace)[pos]? = some d → d.selection.head = .pipeline p i →
    ∃ entry init, latestPipeline (trace.take (pos + 1)) = some (entry, init) ∧
      (∃ buffers routed out, ProbeDerivation.routingBuffers d.probe = some buffers ∧
        put buffers i (ProbeDerivation.produced d.probe) = some (routed, out)) ∧
      (d.out.isSome → i + 1 = init.probes.length)

/-- The complete `lem:paper-buffers` conclusion. -/
def BufferSandboxPreservation (pre : Prefix m h executor prog start) : Prop :=
  SandboxState pre.trace pre.final ∧ RoutingReady pre.trace

/-- The accumulated unfinished result represented by a sandbox. -/
def sandboxResult (sb : Sandbox sig) : Result sig :=
  ⟨none, sb.patch, sb.reads, sb.writes, sb.output⟩

/-- The `lem:paper-sandbox` prefix denotation is required only after a first open
step exists. -/
def CacheablePrefixes (trace : Trace m h .incr prog) (w : World sig) : Prop :=
  ∀ i sb k first, FMap.get w.sandbox i = some sb →
    liveComponent trace i = some k → (openHistory trace k).head? = some first →
    Cacheable m first.selection.head.probe →
      m.denotes first.selection.head.probe sb.input sb.base first.selected.env (sandboxResult sb)

/-- `lem:paper-sandbox`, progressed case of `eq:paper-fold`: a live cacheable
component with at
least one preceding open step folds any admitted next denotation result. The
first open step supplies the probe and the historical environment; the next
call may be open or closing. No host selection, routing, call freshness, or
operational-extension premise occurs here. Reachability supplies both open
flags internally through the proved sandbox invariant. -/
def ProgressedNextCallFolds (pre : Prefix m h .incr prog start)
    (host : HostWellFormed m h) (operational : Operational pre) : Prop :=
  ∀ (i : Nat) (sb : Sandbox sig) (k : Component)
      (first : StepDerivation m h .incr prog) (p : sig.Probe),
    (hs : FMap.get pre.final.sandbox i = some sb) →
    liveComponent pre.trace i = some k →
    (openHistory pre.trace k).head? = some first →
    first.selection.head = .pipeline p i →
    Cacheable m p →
    ∀ (input : Chunk) (result : Result sig),
      m.denotes p input sb.view first.selected.env result →
      let flags := operational.openSandboxes host i sb hs
      m.denotes p (sb.input ++'(flags.1) input) sb.base first.selected.env
        (combineResults (sandboxResult sb) result flags.2)

/-- `lem:paper-sandbox`, zero-open-step case of `eq:paper-fold`: initialized
fields are a
conclusion, not an extra caller premise. The existential equality proof types
the partial concatenations internally. The next call uses its own environment. -/
def ZeroOpenNextCallFolds (trace : Trace m h .incr prog) (w : World sig) : Prop :=
  ∀ (i : Nat) (sb : Sandbox sig) (k : Component) (p : sig.Probe) (env : Env sig),
    FMap.get w.sandbox i = some sb →
    liveComponent trace i = some k →
    openHistory trace k = [] →
    (∃ entry init, latestPipeline trace = some (entry, init) ∧ init.probes[i]? = some p) →
    Cacheable m p →
    ∃ hsb : sb = Sandbox.initial sb.base,
    ∀ (input : Chunk) (result : Result sig),
      m.denotes p input sb.view env result →
      m.denotes p (sb.input ++'(by rw [hsb]; rfl) input) sb.base env
        (combineResults (sandboxResult sb) result (by rw [hsb]; rfl))

/-- `lem:paper-sandbox`, `eq:paper-fold`: the progressed and zero-open-step cases. -/
def NextCallFolds (pre : Prefix m h .incr prog start)
    (host : HostWellFormed m h) (operational : Operational pre) : Prop :=
  ProgressedNextCallFolds pre host operational ∧
    ZeroOpenNextCallFolds pre.trace pre.final

/-- `lem:paper-sandbox`, including current-cache well-formedness and the next-call
fold equation. -/
def CacheablePrefixPreservation (pre : Prefix m h .incr prog start)
    (host : HostWellFormed m h) (operational : Operational pre) : Prop :=
  WellFormedCache m pre.final.cache ∧ CacheablePrefixes pre.trace pre.final ∧
    NextCallFolds pre host operational

/-- A selection can introduce a pipeline before any of its probe steps exist. -/
def selectedPipeline (trace : Trace m h executor prog) (selection : Selection sig) :
    Option (Nat × PipelineInit sig) :=
  match selection.init with
  | some init => some (trace.length, init)
  | none => latestPipeline trace

/-- The component identity immediately after selection, including new slots. -/
def selectedComponent (trace : Trace m h executor prog) (selection : Selection sig) (slot : Nat) :
    Option Component :=
  (selectedPipeline trace selection).map fun pair => .pipeline pair.1 slot

end

end Incr.Incr
