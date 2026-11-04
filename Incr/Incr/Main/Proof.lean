import Incr.Incr.Bisimulation.Proof
import Incr.Incr.Main.Relation

/-!
# Main Theorem 4.3 from the appendix bisimulation

The proof uses `thm:paper-bisimulation` (strong bisimulation) to construct an
existential relation and establish all six step observations.
-/

open Incr
namespace Incr.Incr

variable {sig : Signature} {m : CommandModel sig} {h : Host sig}
  {prog : sig.Prog} {start : World sig}

/-- Main Theorem 4.3, `thm:main-bisimulation`, with every printed conclusion. -/
theorem main_strong_bisimulation (_initial : Initial h prog start)
    (_shape : DenotationShape m) (_commands : WellFormedCommands m)
    (_key : HashInjective m) (_host : HostWellFormed m h)
    (_cache : WellFormedCache m start.cache)
    (witnesses : WitnessMap sig) (_witnesses : WitnessesFor m start.cache witnesses)
    (_initialRecords : TimestampConsistent (worldPaperRecords start ∪ witnessPaperRecords witnesses)) :
    MainBisimulation (m := m) (h := h) (prog := prog) (start := start) witnesses := by
  exact main_bisimulation_of_strong_bisimulation witnesses
    (strong_bisimulation _initial _shape _commands _key _host _cache
      witnesses _witnesses _initialRecords)

end Incr.Incr
