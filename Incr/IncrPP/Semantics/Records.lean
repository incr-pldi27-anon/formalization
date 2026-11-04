import Incr.IncrPP.Semantics.NormalizedRecords
import Incr.Model.Records

/-!
# Whole-map records of live executions (E.3)

This inventory retains actual worlds, snapshots, patches, calls, and semantic
application results. It does not add hypothetical sandbox views.
-/

namespace Incr.IncrPP

noncomputable section

variable {sig : Signature}

/-- Whole patches in an actual current cache. -/
def cachePaperRecords (cache : Cache sig) : RecordCollection sig :=
  {record | ∃ key memo, FMap.get cache key = some memo ∧ record = memo.patch}

/-- Whole historical filesystems of the chosen witness family. -/
def witnessPaperRecords (witnesses : WitnessMap sig) : RecordCollection sig :=
  {record | ∃ key witness, FMap.get witnesses key = some witness ∧ record = recordOfFS witness.fs}

/-- The live filesystem, actual cache patches, and every sandbox's snapshot and patch. -/
def worldPaperRecords (world : World sig) : RecordCollection sig :=
  {recordOfFS world.fs} ∪ cachePaperRecords world.cache ∪
    {record | ∃ slot sb, FMap.get world.sandbox slot = some sb ∧
      (record = recordOfFS sb.base ∨ record = sb.patch)}

/-- An actual executed call's filesystem. Hits contribute none. -/
def StepDerivation.callPaperRecords {m : CommandModel sig} {h : Host sig}
    {executor : Executor} {prog : sig.Prog} (d : StepDerivation m h executor prog) : RecordCollection sig :=
  {record | ∃ fs, ProbeDerivation.callFS d.probe = some fs ∧ record = recordOfFS fs}

/-- The whole result of the actual live filesystem application. -/
def StepDerivation.applicationPaperRecords {m : CommandModel sig} {h : Host sig}
    {executor : Executor} {prog : sig.Prog} (d : StepDerivation m h executor prog) : RecordCollection sig :=
  {recordOfFS (applyPatch d.selected.fs (ProbeDerivation.appliedPatch d.probe))}

/-- All actual step worlds, selected result or memo patch, replay patch, call,
and semantic application result. -/
def StepDerivation.paperRecords {m : CommandModel sig} {h : Host sig}
    {executor : Executor} {prog : sig.Prog} (d : StepDerivation m h executor prog) : RecordCollection sig :=
  worldPaperRecords d.before ∪ worldPaperRecords d.selected ∪ worldPaperRecords d.after ∪
    {(ProbeDerivation.result d.probe).patch} ∪ d.callPaperRecords ∪
    {ProbeDerivation.appliedPatch d.probe} ∪ d.applicationPaperRecords

/-- The initial world and all actual steps of a trace. -/
def tracePaperRecords {m : CommandModel sig} {h : Host sig} {executor : Executor}
    {prog : sig.Prog} (start : World sig) (trace : Trace m h executor prog) : RecordCollection sig :=
  worldPaperRecords start ∪ {record | ∃ d ∈ trace, record ∈ d.paperRecords}

/-- Whole-map records of an initial connected prefix. -/
def Prefix.paperRecords {m : CommandModel sig} {h : Host sig} {executor : Executor}
    {prog : sig.Prog} {start : World sig} (pre : Prefix m h executor prog start) : RecordCollection sig :=
  tracePaperRecords start pre.trace

/-- A permitted selected world adds its actual records without requiring a probe. -/
def Prefix.selectedPaperRecords {m : CommandModel sig} {h : Host sig} {executor : Executor}
    {prog : sig.Prog} {start : World sig} (pre : Prefix m h executor prog start)
    (selected : World sig) : RecordCollection sig := pre.paperRecords ∪ worldPaperRecords selected

end
end IncrPP
end Incr
