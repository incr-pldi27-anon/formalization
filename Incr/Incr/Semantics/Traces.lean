import Incr.Incr.Semantics.Host
import Incr.Incr.Semantics.Probe

/-!
# Whole-step derivations and raw runs (A.2, `def:paper-terminal`)

A whole step retains the host selection and a probe-rule derivation.
A trace is a list of these whole steps, not a separate list of action records.
`Connected` relates the endpoints. `Prefix` adds an initial-world proof, and
`Run` adds host completion. Execution conditions remain separate predicates.
-/

open Incr
namespace Incr.Incr

variable {sig : Signature}

/-- A recorded `Step` or `Step-Vanilla` derivation. Its probe witness retains
all call or replay data. No unvalidated event record is stored. -/
structure StepDerivation (m : CommandModel sig) (h : Host sig)
    (executor : Executor) (prog : sig.Prog) where
  before : World sig
  selection : Selection sig
  selected : World sig
  after : World sig
  out : Option Chunk
  host : h.select prog before selection selected
  probe : ProbeDerivation m executor selected selection.head after out

/-- The whole-step rule skeleton. Pair connected derivations with
`Operational` under `DenotationShape` to obtain the paper execution domain. -/
def Step (m : CommandModel sig) (h : Host sig) (executor : Executor)
    (prog : sig.Prog) (w : World sig) (head : Head sig) (w' : World sig) : Prop :=
  ∃ d : StepDerivation m h executor prog,
    d.before = w ∧ d.selection.head = head ∧ d.after = w'

/-- A raw sequence of recorded whole steps, before endpoint checks. -/
abbrev Trace (m : CommandModel sig) (h : Host sig) (executor : Executor) (prog : sig.Prog) :=
  List (StepDerivation m h executor prog)

/-- The endpoints of successive recorded steps connect. The executor is fixed. -/
inductive Connected {m : CommandModel sig} {h : Host sig}
    {executor : Executor} {prog : sig.Prog} :
    World sig → Trace m h executor prog → World sig → Prop
  | nil (w : World sig) : Connected w [] w
  | cons (d : StepDerivation m h executor prog) (rest : Trace m h executor prog)
      (final : World sig) (tail : Connected d.after rest final) :
      Connected d.before (d :: rest) final

/-- A raw prefix from an initial world. Freshness and record consistency are
not built into this type. -/
structure Prefix (m : CommandModel sig) (h : Host sig) (executor : Executor)
    (prog : sig.Prog) (start : World sig) where
  trace : Trace m h executor prog
  final : World sig
  initial : Initial h prog start
  connected : Connected start trace final

/-- A raw terminating execution. Completion introduces no new exit status. -/
structure Run (m : CommandModel sig) (h : Host sig) (executor : Executor)
    (prog : sig.Prog) (start : World sig) extends Prefix m h executor prog start where
  completion : h.complete prog final

/-- A.2: concatenate returned bytes. Internal routing contributes no bytes,
and EOF on one command does not stop output from later commands. -/
def terminal {m : CommandModel sig} {h : Host sig} {executor : Executor} {prog : sig.Prog}
    (trace : Trace m h executor prog) : Bytes :=
  trace.flatMap fun d => (d.out.map Chunk.bytes).getD []

/-- Only path presence, file contents, exit status, and terminal bytes are observed. -/
structure Observation (sig : Signature) where
  contents : sig.Path → Option sig.Content
  status : Nat
  terminal : Bytes

/-- The final observation excludes timestamps, caches, and derivation witnesses. -/
def Run.observation {m : CommandModel sig} {h : Host sig} {executor : Executor}
    {prog : sig.Prog} {start : World sig} (run : Run m h executor prog start) : Observation sig :=
  ⟨fun q => (FMap.get run.final.fs q).map File.content, run.final.ec, terminal run.trace⟩

end Incr.Incr
