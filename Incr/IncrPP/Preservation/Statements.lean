import Incr.IncrPP.WellFormedness.Boundary
import Incr.IncrPP.Preservation.BufferOrder
import Incr.IncrPP.Preservation.ClosingOrder
import Incr.IncrPP.Preservation.Snapshots
import Incr.IncrPP.Preservation.LiveHistory
import Incr.IncrPP.Preservation.ForeignStability

/-!
# E.4 and E.5: live buffers, path sets, and exit-order consequences

Definitions retain endpoint and post-selection clauses. `RoutingReady`
spells out component-rule premises without assuming the `put` conclusion.
The common buffer, closing, routing, and snapshot package and the live
history/path package are proved separately, then combined in E.4.
-/
namespace Incr.IncrPP

open Incr
noncomputable section
variable {sig : Signature} {m : CommandModel sig} {h : Host sig}
  {executor : Executor} {prog : sig.Prog} {start : World sig}

/-- Open-rule premises other than routing. -/
def OpenRoutingReady (m : CommandModel sig) (executor : Executor) (w : World sig)
    (p : sig.Probe) (i : Nat) (buffers : FMap Nat Chunk) (output : Chunk) : Prop :=
  ∃ taken remaining r,
    FMap.get w.buffer i = some ⟨taken ++ remaining, .open⟩ ∧
    m.denotes p ⟨taken, .open⟩ w.fs w.env r ∧ r.status = none ∧ r.output.flag = .open ∧
    buffers = w.buffer[i ↦ ⟨remaining, .open⟩] ∧ output = r.output ∧
    (match executor with
    | .vanilla => True
    | .live => ∃ sb, FMap.get w.sandbox i = some sb ∧
        sb.input.flag = .open ∧ sb.output.flag = .open)

/-- Executing close-rule premises other than routing, including all miss policies. -/
def CloseRoutingReady (m : CommandModel sig) (executor : Executor) (w : World sig)
    (p : sig.Probe) (i : Nat) (buffers : FMap Nat Chunk) (output : Chunk) : Prop :=
  ∃ s, ∃ r : Result sig, ∃ es, ∃ flag : r.output.flag = .eof,
    FMap.get w.buffer i = some ⟨s, .eof⟩ ∧
    m.denotes p ⟨s, .eof⟩ w.fs w.env r ∧ r.status = some es ∧
    buffers = w.buffer ∖ i ∧ output = r.output ∧
    (match executor with
    | .vanilla => True
    | .live => ∃ sb, FMap.get w.sandbox i = some sb ∧
        (¬ Cacheable m p ∨ (Cacheable m p ∧
          ∃ (hin : sb.input.flag = .open) (hout : sb.output.flag = .open), ∃ cache,
            CacheUpdate w.cache (cacheKey m p w.env (sb.input ++'hin ⟨s, .eof⟩))
              (accumulatedMemo sb ⟨s, .eof⟩ r es hin hout flag) cache)))

/-- Hit premises without `put`; validity alone does not assume its output guard. -/
def HitRoutingReady (m : CommandModel sig) (w : World sig)
    (p : sig.Probe) (i : Nat) (buffers : FMap Nat Chunk) (output : Chunk) : Prop :=
  ∃ sb : Sandbox sig, ∃ s tail memo applied,
    ∃ (hin : sb.input.flag = .open) (hout : sb.output.flag = .open),
    Cacheable m p ∧ sb.patch = ∅ ∧ FMap.get w.buffer i = some ⟨s, .eof⟩ ∧
    FMap.get w.sandbox i = some sb ∧
    FMap.get w.cache (cacheKey m p w.env (sb.input ++'hin ⟨s, .eof⟩)) = some memo ∧
    Valid m memo.reads memo.writes w.fs ∧
    memo.output = sb.output ++'hout ⟨tail, .eof⟩ ∧ PatchApprox applied memo.patch ∧
    buffers = w.buffer ∖ i ∧ output = ⟨tail, .eof⟩

def RoutingReady (m : CommandModel sig) (executor : Executor) (w : World sig)
    (p : sig.Probe) (i : Nat) (buffers : FMap Nat Chunk) (output : Chunk) : Prop :=
  OpenRoutingReady m executor w p i buffers output ∨
    CloseRoutingReady m executor w p i buffers output ∨
    (executor = .live ∧ HitRoutingReady m w p i buffers output)

/-- E.4's entry-local open history, including all displayed equalities. -/
structure EntryHistory (trace : Trace m h .live prog) (entry i : Nat) (sb : Sandbox sig) : Prop where
  patch : sb.patch = historyPatch (openSteps trace (.pipeline entry i))
  input : concatenate ((openSteps trace (.pipeline entry i)).map
    (fun d => ProbeDerivation.input d.probe)) = some sb.input
  output : concatenate ((openSteps trace (.pipeline entry i)).map
    (fun d => (ProbeDerivation.result d.probe).output)) = some sb.output
  reads : sb.reads = historyReads (openSteps trace (.pipeline entry i))
  writes : sb.writes = historyWriteDeps (openSteps trace (.pipeline entry i))
  writePaths : componentWrites trace (.pipeline entry i) = FMap.dom sb.patch
  accessPaths : componentAccesses trace (.pipeline entry i) =
    FMap.dom sb.patch ∪ FMap.dom sb.reads ∪ FMap.dom sb.writes

/-- E.4's global domain, closing-order, routing, and snapshot clauses. -/
structure BufferProperties (pre : Prefix m h executor prog start) (b : Boundary pre) : Prop where
  buffer : FMap.dom b.world.buffer = b.unclosedSlots
  sandbox : FMap.dom b.world.sandbox = b.unclosedSlots
  closingOrder : ∀ entry i j,
    .pipeline entry i ∈ b.componentDomain → .pipeline entry j ∈ b.componentDomain → i < j →
    ∀ position ∈ closingPositions pre.trace (.pipeline entry j),
      ∃ earlier ∈ closingPositions pre.trace (.pipeline entry i), earlier < position
  routing : ∀ p i buffers output, RoutingReady m executor b.world p i buffers output →
    ∃ next returned, put buffers i output = some (next, returned)
  snapshots : ∀ entry i sb, b.livePipeline entry i → FMap.get b.world.sandbox i = some sb →
    ∃ fs init, b.entry entry = some (fs, init) ∧ sb.base = fs
  vanillaEntries : executor = .vanilla →
    ∀ entry i sb, b.livePipeline entry i → FMap.get b.world.sandbox i = some sb →
      ∃ fs init, b.entry entry = some (fs, init) ∧ sb = Sandbox.initial fs

/-- The live-only part is separately typed, without executor casts or fake traces. -/
def LiveBufferProperties (pre : Prefix m h .live prog start) (b : Boundary pre) : Prop :=
  ∀ entry i sb, b.livePipeline entry i → FMap.get b.world.sandbox i = some sb →
    EntryHistory pre.trace entry i sb

/-- Each printed routing-premise package is defined under buffer order. -/
theorem routingReady_of_bufferOrder (w : World sig) (p : sig.Probe) (i : Nat)
    (buffers : FMap Nat Chunk) (output : Chunk) (ordered : BufferOrder w.buffer)
    (ready : RoutingReady m executor w p i buffers output) :
    ∃ next returned, put buffers i output = some (next, returned) := by
  rcases ready with opening | closing | ⟨_, hit⟩
  · obtain ⟨taken, remaining, r, present, _, _, _, rfl, rfl, _⟩ := opening
    exact put_open_defined_of_bufferOrder ordered present _ _
  · obtain ⟨s, r, es, flag, present, _, _, rfl, rfl, _⟩ := closing
    exact put_close_defined_of_bufferOrder ordered present _
  · obtain ⟨sb, s, tail, memo, applied, hin, hout, _, _, present, _, _, _, _, _, rfl, rfl⟩ := hit
    exact put_close_defined_of_bufferOrder ordered present _

/-- E.4's routing clause holds at endpoints and every permitted selection boundary. -/
theorem Boundary.routing (host : HostWellFormed m h) (pre : Prefix m h executor prog start)
    (operational : Operational pre) (b : Boundary pre) :
    ∀ p i buffers output, RoutingReady m executor b.world p i buffers output →
      ∃ next returned, put buffers i output = some (next, returned) := by
  intro p i buffers output ready
  exact routingReady_of_bufferOrder b.world p i buffers output
    (Boundary.bufferOrder host pre operational b) ready

/-- The complete common E.4 package for both executors and every boundary. -/
theorem buffer_properties (host : HostWellFormed m h) :
    ∀ executor prog start (pre : Prefix m h executor prog start), Operational pre →
      ∀ b : Boundary pre, BufferProperties pre b := by
  intro executor prog start pre operational b
  exact ⟨Boundary.buffers_domain host pre operational b,
    Boundary.sandboxes_domain host pre operational b,
    Boundary.closing_order host pre operational b,
    Boundary.routing host pre operational b,
    Boundary.snapshots host pre operational b,
    Boundary.vanillaEntries host pre operational b⟩

/-- The live-only E.4 history and exact path equations at every permitted boundary. -/
theorem live_buffer_properties (host : HostWellFormed m h) :
    ∀ prog start (pre : Prefix m h .live prog start), Operational pre →
      ∀ b : Boundary pre, LiveBufferProperties pre b := by
  intro prog start pre operational b entry slot sb live present
  have fields := Operational.liveHistories host pre operational b entry slot sb live present
  have paths := HistoryFields.component_paths pre.trace (.pipeline entry slot) sb fields
  have openHistory := openSteps_eq_componentSteps pre.trace (.pipeline entry slot) live.2.2
  refine ⟨?_, ?_, ?_, ?_, ?_, paths.1, paths.2⟩
  · simpa only [openHistory] using fields.patch
  · simpa only [openHistory] using fields.input
  · simpa only [openHistory] using fields.output
  · simpa only [openHistory] using fields.reads
  · simpa only [openHistory] using fields.writes

-- Keep the paper's global assumptions explicit in this structural theorem.
set_option linter.unusedVariables false in
/-- E.4: every prefix and each permitted selection boundary, for both executors. -/
theorem buffers_and_path_sets (shape : DenotationShape m) (commands : WellFormedCommands m)
    (host : HostWellFormed m h) (hash : HashInjective m) :
    (∀ executor prog start (pre : Prefix m h executor prog start), Operational pre →
      ∀ b : Boundary pre, BufferProperties pre b) ∧
    (∀ prog start (pre : Prefix m h .live prog start), Operational pre →
      ∀ b : Boundary pre, LiveBufferProperties pre b) := by
  exact ⟨buffer_properties host, live_buffer_properties host⟩

/-- The interval is one-based, inclusive of the first access and closing step. -/
def NoForeignChanges (trace : Trace m h executor prog) : Prop :=
  ∀ k ∈ componentDomain trace, ∀ q (accessed : q ∈ componentAccesses trace k),
    ∀ pos d, (trace)[pos]? = some d → componentAt trace pos d ≠ some k →
      firstAccess trace k q accessed ≤ paperPosition pos → paperPosition pos ≤ lastPosition trace k →
      FMap.get d.after.fs q = FMap.get d.selected.fs q

/-- An actual extension from this boundary, not a required future continuation. -/
def NextAt {pre : Prefix m h executor prog start} (b : Boundary pre)
    (d : StepDerivation m h executor prog) : Prop :=
  d.before = pre.final ∧
    match b with
    | .final => True
    | .selected selection world _ => d.selection = selection ∧ d.selected = world

/-- E.5's live entry absorption and preservation by any ordered foreign extension. -/
structure EntryStability (pre : Prefix m h .live prog start) (b : Boundary pre)
    (entry i : Nat) (sb : Sandbox sig) : Prop where
  absorbed : applyPatch b.world.fs sb.patch = b.world.fs
  foreign : ∀ (d : StepDerivation m h .live prog) (post : Prefix m h .live prog start),
    NextAt b d → post.trace = pre.trace ++ [d] → post.final = d.after →
    Operational post → ExitOrdered post.trace →
    componentAt post.trace pre.trace.length d ≠ some (.pipeline entry i) →
      ∀ q ∈ FMap.dom sb.patch ∪ FMap.dom sb.reads ∪ FMap.dom sb.writes,
        FMap.get d.after.fs q = FMap.get b.world.fs q

-- Preserve the paper's global hypotheses in this structural theorem.
set_option linter.unusedVariables false in
/-- E.5: prefix closure, protected intervals, absorption, and boundary stability. -/
theorem consequences_of_exit_order (shape : DenotationShape m) (commands : WellFormedCommands m)
    (host : HostWellFormed m h) (hash : HashInjective m) :
    (∀ executor prog start (pre : Prefix m h executor prog start),
      Operational pre → ExitOrdered pre.trace →
      (∀ short : Prefix m h executor prog start, short.trace.IsPrefix pre.trace → ExitOrdered short.trace) ∧
        NoForeignChanges pre.trace) ∧
    (∀ prog start (pre : Prefix m h .live prog start), Operational pre → ExitOrdered pre.trace →
      ∀ (b : Boundary pre) entry i sb, b.livePipeline entry i →
        FMap.get b.world.sandbox i = some sb → EntryStability pre b entry i sb) := by
  constructor
  · intro executor prog start pre operational ordered
    exact ⟨fun short shorter => ExitOrdered.of_trace_isPrefix ordered shorter,
      Operational.noForeignChanges host pre operational ordered⟩
  · intro prog start pre operational ordered b entry i sb live present
    constructor
    · exact Operational.liveAbsorbed host pre operational ordered b entry i sb live present
    · intro d post next joined after postOperational postOrdered foreign q membership
      cases b with
      | final =>
        exact Operational.live_foreign_extension host pre post operational postOperational postOrdered
          .final entry i sb live present d next.1 next.2 joined foreign q membership
      | selected selection world allowed =>
        exact Operational.live_foreign_extension host pre post operational postOperational postOrdered
          (.selected selection world allowed) entry i sb live present d next.1 next.2 joined foreign q membership

end
end IncrPP
end Incr
