import Incr.IncrPP.Semantics.Host
import Incr.IncrPP.Semantics.Probe

/-!
# Raw live whole steps and runs

A whole step retains its host selection and raw probe derivation. Connected
prefixes start at an initial world. Runs add completion, without yet imposing
freshness, replay timestamps, or consistent records.
-/

namespace Incr.IncrPP

variable {sig : Signature}

/-- A recorded Live-Step or Live-Step-Vanilla derivation. -/
structure StepDerivation (m : CommandModel sig) (h : Host sig)
    (executor : Executor) (prog : sig.Prog) where
  before : World sig
  selection : Selection sig
  selected : World sig
  after : World sig
  out : Option Chunk
  host : h.select prog before selection selected
  probe : ProbeDerivation m executor selected selection.head after out

/-- Existential erasure to the paper's labeled whole-step judgment. -/
def Step (m : CommandModel sig) (h : Host sig) (executor : Executor)
    (prog : sig.Prog) (before : World sig) (head : Head sig) (after : World sig) : Prop :=
  ∃ d : StepDerivation m h executor prog,
    d.before = before ∧ d.selection.head = head ∧ d.after = after

/-- A list of retained derivations, before endpoint checks. -/
abbrev Trace (m : CommandModel sig) (h : Host sig) (executor : Executor) (prog : sig.Prog) :=
  List (StepDerivation m h executor prog)

/-- Successive recorded steps have matching world endpoints. -/
inductive Connected {m : CommandModel sig} {h : Host sig}
    {executor : Executor} {prog : sig.Prog} :
    World sig → Trace m h executor prog → World sig → Prop
  | nil (w : World sig) : Connected w [] w
  | cons (d : StepDerivation m h executor prog) (rest : Trace m h executor prog)
      (final : World sig) (tail : Connected d.after rest final) :
      Connected d.before (d :: rest) final

/-- An initial connected prefix, without the ambient execution conditions. -/
structure Prefix (m : CommandModel sig) (h : Host sig) (executor : Executor)
    (prog : sig.Prog) (start : World sig) where
  trace : Trace m h executor prog
  final : World sig
  initial : Initial h prog start
  connected : Connected start trace final

/-- A raw terminating prefix. Operational and cache conditions remain separate. -/
structure Run (m : CommandModel sig) (h : Host sig) (executor : Executor)
    (prog : sig.Prog) (start : World sig) extends Prefix m h executor prog start where
  completion : h.complete prog final

/-- Concatenate returned bytes, not chunks routed internally between slots. -/
def terminal {m : CommandModel sig} {h : Host sig} {executor : Executor} {prog : sig.Prog}
    (trace : Trace m h executor prog) : Bytes :=
  trace.flatMap fun d => (d.out.map Chunk.bytes).getD []

end IncrPP
end Incr
