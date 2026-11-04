import Incr.IncrPP.Bisimulation.RunLifting

/-!
# E.12: terminating live soundness statement

The paper statement of `thm:paper-live-sound`, without its proof. The proof
lives in `Incr.IncrPP.Soundness.Proof`, which imports this module.

Both source and target are operational terminating runs consistent with their
initial cache. The live run's final cache is well formed in both directions.
All observations retain live/vanilla ordering, including the reverse source
case. This interface does not assert termination or determinism.

`DenotationShape` is the shared model-typing boundary, not a fifth
`def:paper-command-wf` command clause. Its paper-model map remains part of the
transitive exactness review.

This module stays proof-free so the comparator challenge can state E.12
without importing the live proof.
-/

namespace Incr.IncrPP

variable {sig : Signature}

/-- E.12's two directions with every observation and final live-cache conclusion. -/
def TerminatingSoundness (m : CommandModel sig) (h : Host sig)
    (prog : sig.Prog) (start : World sig) : Prop :=
  (∀ source : AdmittedRun m h .live prog start,
    ∃ target : AdmittedRun m h .vanilla prog start,
      SameProbeSchedule source.run.trace target.run.trace ∧
      SameEnvironments source.run.trace target.run.trace ∧
      SameSuppliedInputs source.run.trace target.run.trace ∧
      terminal source.run.trace = terminal target.run.trace ∧
      source.run.final.ec = target.run.final.ec ∧
      FSApprox source.run.final.fs target.run.final.fs ∧
      WellFormedCache m source.run.final.cache) ∧
  (∀ source : AdmittedRun m h .vanilla prog start,
    ∃ target : AdmittedRun m h .live prog start,
      SameProbeSchedule target.run.trace source.run.trace ∧
      SameEnvironments target.run.trace source.run.trace ∧
      SameSuppliedInputs target.run.trace source.run.trace ∧
      terminal target.run.trace = terminal source.run.trace ∧
      target.run.final.ec = source.run.final.ec ∧
      FSApprox target.run.final.fs source.run.final.fs ∧
      WellFormedCache m target.run.final.cache)

/-- E.12 assumptions, with the shared model's result-typing discipline explicit. -/
def SoundnessStatement (m : CommandModel sig) (h : Host sig)
    (prog : sig.Prog) (start : World sig) : Prop :=
  DenotationShape m →
  WellFormedCommands m →
  HostWellFormed m h →
  HashInjective m →
  Initial h prog start →
  WellFormedCache m start.cache →
  WellFormedProgram m h prog start →
  TerminatingSoundness m h prog start

end Incr.IncrPP
