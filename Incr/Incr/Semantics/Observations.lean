import Incr.Incr.Semantics.Traces

/-!
# Paper input observations

The host section and H3 specify input through world changes. An optional
annotation on a Lean selection is not a separate paper observation.
The `thm:paper-sound` conclusion says "supplied inputs"
(`appendix.tex:1523-1524`). Its proof
specifies "consumed input and external input deliveries"
(`appendix.tex:1546-1548`). We use that explicit list to interpret the phrase:
`SameSuppliedInputs` compares both host input effects and consumed probe chunks.
The explanation after `def:paper-bisim-relation` (`appendix.tex:926-933`)
identifies consumed input
from probe-step buffers and external input from host-selection worlds.
This is the paper's proof-specific interpretation, not an additional input
agreement chosen because it follows from stronger conclusions elsewhere.
Probe assignments, initialization records, and unused pipeline stdin are not
part of this observer.
-/

open Incr
namespace Incr.Incr

variable {sig : Signature} {m : CommandModel sig} {h : Host sig}
  {executor executor' : Executor} {prog : sig.Prog}

/-- The three host input mechanisms from the host section and H3.
The absence of a world change is not a separate empty-open delivery event. -/
inductive HostInputEffect where
  | none
  | standalone (input : Chunk)
  | initial (input : Chunk)
  | append (input : Chunk)
  deriving DecidableEq, Repr

/-- Input supplied by one host selection, read from its paper worlds.
For operational prefixes under H1/H3, a later slot-zero change is exactly
an append to an open buffer. `drop` extracts its supplied suffix.
Fallback branches only make this projection total on raw derivations. -/
def StepDerivation.hostInput (d : StepDerivation m h executor prog) : HostInputEffect :=
  match d.selection.head with
  | .standalone _ => .standalone d.selected.stdin
  | .pipeline _ _ =>
    match d.selection.init with
    | some _ =>
      match FMap.get d.selected.buffer 0 with
      | some input => .initial input
      | none => .none
    | none =>
      match FMap.get d.before.buffer 0, FMap.get d.selected.buffer 0 with
      | some before, some after =>
        if before = after then .none
        else .append ⟨after.bytes.drop before.bytes.length, after.flag⟩
      | _, _ => .none

/-- The `thm:paper-sound` ordered probe labels, including pipeline slots. -/
def SameProbeSchedule (left : Trace m h executor prog)
    (right : Trace m h executor' prog) : Prop :=
  left.map (fun d => d.selection.head) = right.map (fun d => d.selection.head)

/-- The `thm:paper-sound` environments at the corresponding probe steps. -/
def SameEnvironments (left : Trace m h executor prog)
    (right : Trace m h executor' prog) : Prop :=
  left.map (fun d => d.selected.env) = right.map (fun d => d.selected.env)

/-- The `thm:paper-sound` "supplied inputs": both external input supplies and
consumed probe
chunks, following the proof of `thm:paper-sound` (`appendix.tex:1546-1548`).
The two conjuncts expose those distinct input boundaries explicitly. -/
def SameSuppliedInputs (left : Trace m h executor prog)
    (right : Trace m h executor' prog) : Prop :=
  left.map StepDerivation.hostInput = right.map StepDerivation.hostInput ∧
    left.map (fun d => ProbeDerivation.input d.probe) =
      right.map (fun d => ProbeDerivation.input d.probe)

end Incr.Incr
