import Incr.Incr.Bisimulation.Proof
import Incr.Incr.Bisimulation.Observations
import Incr.Incr.Bisimulation.RunLifting

/-!
# `thm:paper-sound` (terminating soundness) from the fixed-witness bisimulation

The proof uses `thm:paper-bisimulation` to construct admitted target runs in both
directions.
It preserves the schedule, environments, supplied inputs, terminal output,
status, and filesystem contents.
-/

open Incr
namespace Incr.Incr

variable {sig : Signature} {m : CommandModel sig} {h : Host sig}
  {prog : sig.Prog} {start : World sig}

/-- The `thm:paper-sound` run argument, with the fixed-witness
`thm:paper-bisimulation` result supplied explicitly.
This theorem does not use a numbered proof placeholder. -/
theorem terminating_soundness_of_bisimulation
    (program : WellFormedProgram m h prog start)
    (bisimulations : ∀ witnesses : WitnessMap sig, WitnessesFor m start.cache witnesses →
      TimestampConsistent (worldPaperRecords start ∪ witnessPaperRecords witnesses) →
      StrongBisimulation (m := m) (h := h) (prog := prog) (start := start) witnesses) :
    TerminatingSoundness m h prog start := by
  constructor
  · intro source
    obtain ⟨witnesses, chosen, admissible⟩ := C9.source_witnesses program source
    have bisimulation := bisimulations witnesses chosen (C9.initial_records admissible)
    obtain ⟨vanilla, related⟩ := C9.match_incr bisimulation source.run.toPrefix admissible
    have completed : h.complete prog vanilla.final :=
      (bisimulation.2.2.2 _ _ related).1.mp source.run.completion
    let target : AdmittedRun m h .vanilla prog start :=
      ⟨{ toPrefix := vanilla, completion := completed }, related.vanillaAdmissible.operational,
        C9.admissible_initial_cache chosen related.vanillaAdmissible⟩
    obtain ⟨schedule, environments, supplied⟩ := related.observations
    have observations := (bisimulation.2.2.2 _ _ related).2 source.run.completion
    exact ⟨target, schedule, environments, supplied, observations⟩
  · intro source
    obtain ⟨witnesses, chosen, admissible⟩ := C9.source_witnesses program source
    have bisimulation := bisimulations witnesses chosen (C9.initial_records admissible)
    obtain ⟨incr, related⟩ := C9.match_vanilla bisimulation source.run.toPrefix admissible
    have completed : h.complete prog incr.final :=
      (bisimulation.2.2.2 _ _ related).1.mpr source.run.completion
    let target : AdmittedRun m h .incr prog start :=
      ⟨{ toPrefix := incr, completion := completed }, related.incrAdmissible.operational,
        C9.admissible_initial_cache chosen related.incrAdmissible⟩
    obtain ⟨schedule, environments, supplied⟩ := related.observations
    obtain ⟨terminal, status, filesystem⟩ := (bisimulation.2.2.2 _ _ related).2 completed
    exact ⟨target, schedule.symm, environments.symm,
      ⟨supplied.1.symm, supplied.2.symm⟩, terminal.symm, status.symm,
      FSApprox.of_contents (fun q => (filesystem.contents q).symm)⟩

/-- `thm:paper-sound` / `thm:main-sound` (terminating soundness): terminating
soundness in both executor directions, using the proved `thm:paper-bisimulation`
bisimulation. -/
theorem thm_sound : SoundnessStatement m h prog start := by
  intro initial shape commands key host program cache
  apply terminating_soundness_of_bisimulation program
  intro witnesses chosen initialRecords
  exact strong_bisimulation initial shape commands key host cache witnesses chosen initialRecords

/-- info: 'Incr.Incr.thm_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms thm_sound

end Incr.Incr
