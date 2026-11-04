import Incr.IncrPP.Bisimulation.PrefixSystems
import Incr.IncrPP.Soundness.Proof

/-!
# Distinct main-text live interfaces: initial statement slice

This module states main exit ordering, admissible prefix systems, and
terminating soundness. `MainPreservation` and `MainBisimulation` state the
other two main interfaces. No theorem is proved here.
-/

namespace Incr.IncrPP

noncomputable section

variable {sig : Signature} {m : CommandModel sig} {h : Host sig}
  {executor : Executor} {prog : sig.Prog} {start : World sig}

/-- Main `def:main-live-order`: the printed ordered-pair sharing condition. -/
def MainExitOrdered (trace : Trace m h executor prog) : Prop :=
  ∀ entry i j,
    .pipeline entry i ∈ componentDomain trace →
    .pipeline entry j ∈ componentDomain trace → i ≠ j →
    ∀ q (shared : q ∈ componentWrites trace (.pipeline entry i) ∩
        componentAccesses trace (.pipeline entry j)),
      lastPosition trace (.pipeline entry i) <
          firstAccess trace (.pipeline entry j) q shared.2 ∨
        lastPosition trace (.pipeline entry j) <
          firstAccess trace (.pipeline entry i) q (Or.inr shared.1)

/-- Main program well-formedness covers both operational terminating executors. -/
def MainWellFormedProgram (m : CommandModel sig) (h : Host sig) (prog : sig.Prog)
    (start : World sig) : Prop :=
  ∀ executor (run : Run m h executor prog start),
    Operational run.toPrefix → MainExitOrdered run.trace

/-- Main `def:main-live-prefix-systems`, over the shared ambient execution domain. -/
structure MainAdmissible (witnesses : WitnessMap sig) (pre : Prefix m h executor prog start) : Prop where
  operational : Operational pre
  ordered : MainExitOrdered pre.trace
  timestamps : TimestampConsistent (pre.paperRecords ∪ witnessPaperRecords witnesses)

/-- Main prefix edges use one same-label live host step and two admissible endpoints. -/
def MainPrefixStep (witnesses : WitnessMap sig) (head : Head sig)
    (pre post : Prefix m h executor prog start) : Prop :=
  MainAdmissible witnesses pre ∧ MainAdmissible witnesses post ∧
    ∃ d : StepDerivation m h executor prog,
      d.before = pre.final ∧ d.selection.head = head ∧
      post.trace = pre.trace ++ [d] ∧ post.final = d.after

/-- Main admissible-prefix systems use live-host completion, without future termination. -/
def mainPrefixSystem (executor : Executor) (context : PrefixContext m h prog start) : PrefixSystem sig where
  State := { pre : Prefix m h executor prog start // MainAdmissible context.witnesses pre }
  step := fun pre head post => MainPrefixStep context.witnesses head pre.val post.val
  complete := fun pre => PrefixComplete pre.val

/-- Main `thm:main-live-sound` assumptions and its full terminating observation package. -/
def MainSoundnessStatement (m : CommandModel sig) (h : Host sig)
    (prog : sig.Prog) (start : World sig) : Prop :=
  DenotationShape m →
  WellFormedCommands m →
  HostWellFormed m h →
  HashInjective m →
  Initial h prog start →
  MainWellFormedProgram m h prog start →
  WellFormedCache m start.cache →
  TerminatingSoundness m h prog start

/-- Distinct main terminating soundness theorem. -/
theorem main_soundness : MainSoundnessStatement m h prog start := by
  intro shape commands host hash initial program cache
  exact thm_sound shape commands host hash initial cache program

end
end IncrPP
end Incr
