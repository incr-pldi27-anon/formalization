import Incr.IncrPP.Semantics.Traces
import Incr.IncrPP.Semantics.Views

/-!
# Live run observations

P6 separates external supplies from consumed probe chunks. Initialization
and delivery annotations are not observations of their own identities.
-/

namespace Incr.IncrPP

variable {sig : Signature} {m : CommandModel sig} {h : Host sig}
  {executor executor' : Executor} {prog : sig.Prog}

/-- The external input effects of the paper's host selections. -/
inductive HostInputEffect where
  | none
  | standalone (input : Chunk)
  | initial (input : Chunk)
  | append (input : Chunk)
  deriving DecidableEq, Repr

/-- Read actual world effects. Raw fallback branches do not certify a host law. -/
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

/-- The ordered probe labels, including pipeline slots. -/
def SameProbeSchedule (left : Trace m h executor prog)
    (right : Trace m h executor' prog) : Prop :=
  left.map (fun d => d.selection.head) = right.map (fun d => d.selection.head)

/-- Environments at the corresponding selected probe calls. -/
def SameEnvironments (left : Trace m h executor prog)
    (right : Trace m h executor' prog) : Prop :=
  left.map (fun d => d.selected.env) = right.map (fun d => d.selected.env)

/-- Both external supplies and consumed chunks, not annotation equality. -/
def SameSuppliedInputs (left : Trace m h executor prog)
    (right : Trace m h executor' prog) : Prop :=
  left.map StepDerivation.hostInput = right.map StepDerivation.hostInput ∧
    left.map (fun d => ProbeDerivation.input d.probe) =
      right.map (fun d => ProbeDerivation.input d.probe)

end IncrPP
end Incr
