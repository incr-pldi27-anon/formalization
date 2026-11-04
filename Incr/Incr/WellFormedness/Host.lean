import Incr.Incr.WellFormedness.Components
import Mathlib.Data.Finset.Sort

/-!
# Host requirements stated over recorded prefixes

This is an independent candidate for paper `def:paper-host-wf`, not an alias for
the current `HostWellFormed`. H1--H3 constrain operational prefixes, whether or
not they
terminate. H2 constrains actual recorded component steps and selections of
progressed components. O1 reads its component-preservation sentence at the
selection boundary, as used in `lem:paper-hit-completion` and
`thm:paper-bisimulation`. This is an explicit elaboration
of the paper assumption, not a consequence proved from the old steps-only law.
See `docs/recorded-interpretation-decisions.md` for alternatives.
H4 concerns host selection only, not command simulation or run matching.
-/

open Incr
namespace Incr.Incr

noncomputable section

variable {sig : Signature}

/-- Pipeline entry initializes all buffers together. -/
def initialBuffers (init : PipelineInit sig) : FMap Nat Chunk :=
  (init.probes.mapIdx fun i _ =>
    (⟨i, if i = 0 then init.input else Chunk.emptyOpen⟩ : Sigma (fun _ : Nat => Chunk))).toFinmap

/-- Every entry snapshot copies the live filesystem at pipeline entry. -/
def initialSandboxes (init : PipelineInit sig) (fs : FS sig) : FMap Nat (Sandbox sig) :=
  (init.probes.mapIdx fun i _ =>
    (⟨i, Sandbox.initial fs⟩ : Sigma (fun _ : Nat => Sandbox sig))).toFinmap

/-- Probe assignment belongs to the current pipeline entry. -/
def assignedProbes {m : CommandModel sig} {h : Host sig} {executor : Executor} {prog : sig.Prog}
    (trace : Trace m h executor prog) (selection : Selection sig) : Option (List sig.Probe) :=
  match selection.init with
  | some init => some init.probes
  | none => (latestPipeline trace).map fun entry => entry.2.probes

/-- H1: field preservation, pipeline entry, and stable slot assignment. -/
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

/-- H2: each recorded component step retains its first step's probe, slot, and environment. -/
def ComponentEnvironments {m : CommandModel sig} {h : Host sig}
    {executor : Executor} {prog : sig.Prog} (trace : Trace m h executor prog) : Prop :=
  ∀ k first, (componentSteps trace k).head? = some first →
    ∀ d, d ∈ componentSteps trace k →
      d.selection.head = first.selection.head ∧ d.selected.env = first.selected.env

/-- O1: selection of an existing component preserves its recorded environment,
even before the selected probe executes. A new pipeline or a component with
no preceding step has no fixed first-step environment yet. Other components
can use different environments. `lem:paper-hit-completion` and the backward
`thm:paper-bisimulation` direction use this boundary law
(`appendix.tex:829-832,1319-1322`), citing H2's preservation of unclosed
components. This law is explicit, not derived from `ComponentEnvironments`. -/
def ComponentSelectionEnvironments {m : CommandModel sig} {h : Host sig}
    {executor : Executor} {prog : sig.Prog} (trace : Trace m h executor prog)
    (selection : Selection sig) (selected : World sig) : Prop :=
  ∀ p i k previous, selection.init = none → selection.head = .pipeline p i →
    liveComponent trace i = some k → previous ∈ componentSteps trace k →
      selected.env = previous.selected.env

/-- H3: delivery appends to an existing open slot-zero buffer. -/
def InputDelivery (before : World sig) (selection : Selection sig) (selected : World sig) : Prop :=
  match selection.init with
  | some _ => selection.delivery = none
  | none =>
    match selection.delivery with
    | none => selected.buffer = before.buffer
    | some chunk =>
      ∃ s, FMap.get before.buffer 0 = some ⟨s, .open⟩ ∧
        selected.buffer = before.buffer[0 ↦ ⟨s ++ chunk.bytes, chunk.flag⟩]

/-- The observable host control and input state agree. -/
def ControlAgree (left right : World sig) : Prop :=
  left.pc = right.pc ∧ left.ec = right.ec ∧ left.env = right.env ∧
    left.buffer = right.buffer ∧ left.stdin = right.stdin

/-- A fixed enumeration makes the pending overlay a function. Under H4's
pairwise-disjointness premise, the enumeration order has no semantic role. -/
def pendingPatch (w : World sig) : Patch sig :=
  (w.sandbox.keys.sort (· ≤ ·)).foldl (fun acc i =>
    match FMap.get w.sandbox i with
    | none => acc
    | some sb => acc ⊎ sb.patch) ∅

/-- Different live components have disjoint staged patch domains. -/
def PendingDisjoint (w : World sig) : Prop :=
  ∀ i j sb sb', i ≠ j →
    FMap.get w.sandbox i = some sb → FMap.get w.sandbox j = some sb' →
      Disjoint (FMap.dom sb.patch) (FMap.dom sb'.patch)

/-- H4 compares initialization occurrence and slot assignments, not the entire
Lean initialization record. Entry input is observed through selected buffers.
O3 follows the `thm:paper-bisimulation` matched-selection proof
(`appendix.tex:1061-1070,1254-1263`).
Delivery annotations are not compared. -/
def MatchingSelections (left right : Selection sig) (selected selected' : World sig) : Prop :=
  left.head = right.head ∧ left.init.map (·.probes) = right.init.map (·.probes) ∧
    selected.pc = selected'.pc ∧ selected.env = selected'.env ∧
    selected.buffer = selected'.buffer ∧ selected.stdin = selected'.stdin

/-- Match one host selection. No probe step or command result occurs here. -/
def SelectionsTransport (h : Host sig) (prog : sig.Prog) (left right : World sig) : Prop :=
  ∀ selection selected, h.select prog left selection selected →
    ∃ selection' selected', h.select prog right selection' selected' ∧
      MatchingSelections selection selection' selected selected'

/-- `def:paper-host-wf` (host well-formedness): host assumptions over the
recorded prefixes. Each field corresponds to a paper clause. Their adequacy for
the pending soundness proof remains a proof obligation. O1's
selected-environment clause
is the documented working reading of H2, not an unnoticed strengthening. -/
structure HostWellFormed (m : CommandModel sig) (h : Host sig) : Prop where
  selectionDiscipline : ∀ executor prog start (pre : Prefix m h executor prog start),
    Operational pre → ∀ selection selected, h.select prog pre.final selection selected →
      SelectionDiscipline pre.trace pre.final selection selected
  componentEnvironments : ∀ executor prog start (pre : Prefix m h executor prog start),
    Operational pre → ComponentEnvironments pre.trace
  /-- O1: the host preserves the fixed environment when it selects a progressed
  component. This field applies even if no operational probe extension follows. -/
  componentSelectionEnvironments : ∀ executor prog start
      (pre : Prefix m h executor prog start),
    Operational pre → ∀ selection selected, h.select prog pre.final selection selected →
      ComponentSelectionEnvironments pre.trace selection selected
  inputDelivery : ∀ executor prog start (pre : Prefix m h executor prog start),
    Operational pre → ∀ selection selected, h.select prog pre.final selection selected →
      InputDelivery pre.final selection selected
  /-- The two prefixes may start from independent initial worlds; only the
  script and the final-world premises are shared.
  O3 uses absolute recorded entry positions and slots as correspondence
  keys, as in `def:paper-bisim-relation`. The prefixes still have independent
starts and lengths.
  This convention restricts which independently chosen pairs trigger H4.
  It is the convention used by the synchronized
`thm:paper-bisimulation`/`thm:paper-sound` proof, not a proof that
  every possible invocation-renaming interpretation of H4 is equivalent.
  See `docs/recorded-interpretation-decisions.md` for alternatives. -/
  selectionWithPending : ∀ prog (incrStart vanillaStart : World sig)
    (incr : Prefix m h .incr prog incrStart) (vanilla : Prefix m h .vanilla prog vanillaStart),
    Operational incr → Operational vanilla →
    (∀ i, i ∈ FMap.dom incr.final.sandbox →
      liveComponent incr.trace i = liveComponent vanilla.trace i) →
    FMap.dom incr.final.sandbox = FMap.dom vanilla.final.sandbox →
    ControlAgree incr.final vanilla.final → PendingDisjoint incr.final →
    FSApprox vanilla.final.fs (applyPatch incr.final.fs (pendingPatch incr.final)) →
      SelectionsTransport h prog incr.final vanilla.final ∧
      SelectionsTransport h prog vanilla.final incr.final
  completionEmpty : ∀ prog w, h.complete prog w → w.buffer = ∅ ∧ w.sandbox = ∅
  completionNoSelection : ∀ prog w, h.complete prog w →
    ∀ selection selected, ¬ h.select prog w selection selected
  completionInvariance : ∀ prog w w',
    w.buffer = ∅ → w.sandbox = ∅ → w'.buffer = ∅ → w'.sandbox = ∅ →
    w.pc = w'.pc → w.ec = w'.ec → w.env = w'.env → w.stdin = w'.stdin →
    FSApprox w.fs w'.fs →
      (h.complete prog w ↔ h.complete prog w')

end

end Incr.Incr
