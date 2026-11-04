import Incr.Incr.Bisimulation.Steps

/-!
# Prefix properties (`lem:paper-bisim-prefix`) and the strong bisimulation
(`thm:paper-bisimulation`)

These results concern admissible prefixes, not only prefixes of terminating
runs. They do not assume program well-formedness to infer prefix isolation.
-/

open Incr
namespace Incr.Incr

variable {sig : Signature} {m : CommandModel sig} {h : Host sig}
  {prog : sig.Prog} {start : World sig}

/-- `lem:paper-bisim-prefix` (prefix properties): witness provenance,
frame/slice equations, and hit-path accounting, also immediately after host
selection. -/
theorem paper_bisim_prefix (_shape : DenotationShape m)
    (_commands : WellFormedCommands m) (_key : HashInjective m)
    (_host : HostWellFormed m h) (_cache : WellFormedCache m start.cache)
    (witnesses : WitnessMap sig) (_witnesses : WitnessesFor m start.cache witnesses)
    (_initialRecords : TimestampConsistent (worldPaperRecords start ∪ witnessPaperRecords witnesses))
    (pre : Prefix m h .incr prog start) (_admissible : Admissible witnesses pre) :
    BisimPrefixProperties witnesses pre := by
  exact PrefixProperties.paper_bisim_prefix _shape _commands _key _host _cache
    witnesses _witnesses _initialRecords pre _admissible

/-- `thm:paper-bisimulation` (strong bisimulation): strong bisimulation of the
paper relation, with fixed initial-cache witnesses and separate per-prefix
consistency. -/
theorem strong_bisimulation (_initial : Initial h prog start) (_shape : DenotationShape m)
    (_commands : WellFormedCommands m) (_key : HashInjective m)
    (_host : HostWellFormed m h) (_cache : WellFormedCache m start.cache)
    (witnesses : WitnessMap sig) (_witnesses : WitnessesFor m start.cache witnesses)
    (_initialRecords : TimestampConsistent (worldPaperRecords start ∪ witnessPaperRecords witnesses)) :
    StrongBisimulation (m := m) (h := h) (prog := prog) (start := start) witnesses := by
  refine ⟨C8Steps.forward_steps _initial _shape _commands _key _host _cache
    witnesses _witnesses _initialRecords,
    C8Steps.backward_steps _initial _shape _commands _key _host _cache
      witnesses _witnesses _initialRecords, ?_, BisimulationBasis.completion _host⟩
  intro initial
  exact BisimulationBasis.initial initial _shape _commands _key _host _cache
    witnesses _initialRecords

end Incr.Incr
