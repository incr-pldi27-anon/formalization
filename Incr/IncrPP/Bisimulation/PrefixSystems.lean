import Incr.IncrPP.WellFormedness.ExitOrder

/-!
# E.8: live admissible prefix systems

Initial cache witnesses are fixed parameters of a comparison. Each prefix
has its own timestamp records jointly consistent with these fixed witnesses.
No cross-history consistency or terminating continuation is required.
-/

namespace Incr.IncrPP

noncomputable section

variable {sig : Signature} {m : CommandModel sig} {h : Host sig}
  {executor : Executor} {prog : sig.Prog} {start : World sig}

/-- The fixed initial context printed immediately before E.8. -/
structure PrefixContext (m : CommandModel sig) (h : Host sig) (prog : sig.Prog)
    (start : World sig) where
  initial : Initial h prog start
  cache : WellFormedCache m start.cache
  witnesses : WitnessMap sig
  chosen : WitnessesFor m start.cache witnesses
  consistent : TimestampConsistent (worldPaperRecords start ∪ witnessPaperRecords witnesses)

/-- E.8 admissibility over raw prefixes includes the ambient execution domain. -/
structure Admissible (witnesses : WitnessMap sig) (pre : Prefix m h executor prog start) : Prop where
  operational : Operational pre
  ordered : ExitOrdered pre.trace
  timestamps : TimestampConsistent (pre.paperRecords ∪ witnessPaperRecords witnesses)

/-- Normalized proof support for the fixed initial witness family. -/
theorem PrefixContext.normalizedConsistent (context : PrefixContext m h prog start) :
    TimestampCompatible (worldRecords start ++ witnessRecords context.witnesses) :=
  (worldPaperRecords_witness_consistent_iff start context.witnesses).mp context.consistent

/-- Normalized proof support for one separately admitted prefix. -/
theorem Admissible.normalizedWitnesses {witnesses : WitnessMap sig}
    {pre : Prefix m h executor prog start} (admissible : Admissible witnesses pre) :
    TimestampCompatible (pre.records ++ witnessRecords witnesses) :=
  (pre.paperRecords_witness_consistent_iff witnesses).mp admissible.timestamps

/-- E.8 edges require both endpoints, the same label, and one recorded host step. -/
def PrefixStep (witnesses : WitnessMap sig) (head : Head sig)
    (pre post : Prefix m h executor prog start) : Prop :=
  Admissible witnesses pre ∧ Admissible witnesses post ∧
    ∃ d : StepDerivation m h executor prog,
      d.before = pre.final ∧ d.selection.head = head ∧
      post.trace = pre.trace ++ [d] ∧ post.final = d.after

/-- Prefix-system completion uses the same live host completion relation. -/
def PrefixComplete (pre : Prefix m h executor prog start) : Prop :=
  h.complete prog pre.final

/-- A labeled transition system with an explicit state and completion domain. -/
structure PrefixSystem (sig : Signature) where
  State : Type
  step : State → Head sig → State → Prop
  complete : State → Prop

/-- E.8 packages either executor's admissible prefixes as system states. -/
def prefixSystem (executor : Executor) (context : PrefixContext m h prog start) : PrefixSystem sig where
  State := { pre : Prefix m h executor prog start // Admissible context.witnesses pre }
  step := fun pre head post => PrefixStep context.witnesses head pre.val post.val
  complete := fun pre => PrefixComplete pre.val

end
end IncrPP
end Incr
