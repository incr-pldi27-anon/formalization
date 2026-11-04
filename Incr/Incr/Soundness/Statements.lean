import Incr.Incr.WellFormedness.Host
import Incr.Assumptions.Commands

/-!
# The admitted-run soundness statement (paper `thm:paper-sound`)

Design B is the only public interface. The alternatives considered earlier
remain in the design history, not in the Lean API. A source and its matching
target both carry the shared execution and cache-witness conditions.
The three conclusions are written explicitly, as in the paper.
-/

open Incr
namespace Incr.Incr

variable {sig : Signature}

/-- The matching-run conclusion of `thm:paper-sound` in one direction. -/
def SoundnessDirection (m : CommandModel sig) (h : Host sig) (prog : sig.Prog)
    (start : World sig) (sourceExecutor targetExecutor : Executor) : Prop :=
  ∀ source : AdmittedRun m h sourceExecutor prog start,
    ∃ target : AdmittedRun m h targetExecutor prog start,
      SameProbeSchedule source.run.trace target.run.trace ∧
      SameEnvironments source.run.trace target.run.trace ∧
      SameSuppliedInputs source.run.trace target.run.trace ∧
      terminal source.run.trace = terminal target.run.trace ∧
      source.run.final.ec = target.run.final.ec ∧
      FSApprox source.run.final.fs target.run.final.fs

/-- `thm:paper-sound` and `thm:main-sound`: terminating soundness in both
 directions. This proposition does not assert termination or determinism. -/
def TerminatingSoundness (m : CommandModel sig) (h : Host sig)
    (prog : sig.Prog) (start : World sig) : Prop :=
  SoundnessDirection m h prog start .incr .vanilla ∧
    SoundnessDirection m h prog start .vanilla .incr

/-- The full `thm:paper-sound` theorem type. `DenotationShape` states the model's
result typing discipline. `def:paper-command-wf` and `asm:paper-key` remain
distinct hypotheses, as in the paper.
`Incr.Incr.thm_sound` proves this statement in `Incr.Incr.Soundness.Proof`. -/
def SoundnessStatement (m : CommandModel sig) (h : Host sig)
    (prog : sig.Prog) (start : World sig) : Prop :=
  Initial h prog start →
  DenotationShape m →
  WellFormedCommands m →
  HashInjective m →
  HostWellFormed m h →
  WellFormedProgram m h prog start →
  WellFormedCache m start.cache →
  TerminatingSoundness m h prog start

end Incr.Incr
