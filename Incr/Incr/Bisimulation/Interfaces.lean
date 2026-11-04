import Incr.Incr.Soundness.Statements

/-!
# Bookkeeping facts for recorded executions

The former alternative soundness APIs are no longer present. These small
facts concern composition, observations, and execution conditions only.
The numbered paper proofs live separately.
-/

open Incr
namespace Incr.Incr

variable {sig : Signature} {m : CommandModel sig} {h : Host sig}
  {prog : sig.Prog} {start : World sig}

/-- A whole step exists exactly when a selection and a probe derivation compose. -/
theorem step_iff_selection_probe {executor : Executor} {w head w'} :
    Step m h executor prog w head w' ↔
      ∃ selection selected out,
        selection.head = head ∧ h.select prog w selection selected ∧
          ProbeStep m executor selected selection.head w' out := by
  constructor
  · rintro ⟨d, rfl, rfl, rfl⟩
    exact ⟨d.selection, d.selected, d.out, rfl, d.host, ⟨d.probe⟩⟩
  · rintro ⟨selection, selected, out, hhead, hhost, ⟨probe⟩⟩
    exact ⟨⟨w, selection, selected, w', out, hhost, probe⟩, rfl, hhead, rfl⟩

/-- Cache-witness consistency implies internal timestamp consistency. -/
theorem InitialCacheConsistent.timestamps {executor : Executor}
    {pre : Prefix m h executor prog start} (hc : InitialCacheConsistent pre) :
    TimestampCompatible pre.records := by
  obtain ⟨_, _, hts⟩ := hc
  apply pre.paperRecords_consistent_iff.mp
  exact TimestampConsistent.mono (fun _ member => Or.inl (Or.inl member)) hts

/-- Terminal concatenation does not stop at an EOF chunk. -/
theorem terminal_append {executor : Executor} (left right : Trace m h executor prog) :
    terminal (left ++ right) = terminal left ++ terminal right := by
  exact List.flatMap_append

/-- Equal probe schedules imply equal trace length. -/
theorem SameProbeSchedule.length_eq {executor executor' : Executor}
    {left : Trace m h executor prog} {right : Trace m h executor' prog}
    (hs : SameProbeSchedule left right) : left.length = right.length := by
  have heq := congrArg List.length hs
  simpa only [List.length_map] using heq

/-- The observation helper packages exactly the three `thm:paper-sound`
conclusions. -/
theorem observation_eq_iff {executor executor' : Executor}
    (source : Run m h executor prog start) (target : Run m h executor' prog start) :
    source.observation = target.observation ↔
      terminal source.trace = terminal target.trace ∧
      source.final.ec = target.final.ec ∧ FSApprox source.final.fs target.final.fs := by
  constructor
  · intro heq
    exact ⟨congrArg Observation.terminal heq, congrArg Observation.status heq,
      FSApprox.of_contents (fun q => congrFun (congrArg Observation.contents heq) q)⟩
  · rintro ⟨hterminal, hstatus, hfs⟩
    change Observation.mk (fun q => (FMap.get source.final.fs q).map File.content)
        source.final.ec (terminal source.trace) =
      Observation.mk (fun q => (FMap.get target.final.fs q).map File.content)
        target.final.ec (terminal target.trace)
    rw [funext hfs.contents, hstatus, hterminal]

/-- Program well-formedness supplies isolation for admitted runs. -/
theorem AdmittedRun.isolated {executor : Executor}
    (programWF : WellFormedProgram m h prog start)
    (run : AdmittedRun m h executor prog start) : Isolated run.run.trace :=
  programWF executor run.run run.operational

end Incr.Incr
