import Incr.IncrPP.Semantics.RecordFacts

/-!
# Live records and execution conditions (E.3)

Execution records retain whole live filesystem and patch maps. Normalized file
occurrences are proof support, not the public consistency collection.
-/

namespace Incr.IncrPP

noncomputable section

variable {sig : Signature}

/-- Replay write timestamps come from the same memo path or are fresh globally. -/
def ReplayTimestamps (applied memo : Patch sig) (fs : FS sig) : Prop :=
  ∀ q file, FMap.get applied q = some (.write file) →
    (∃ recorded, FMap.get memo q = some (.write recorded) ∧ file.mtime = recorded.mtime) ∨
      ∀ q' previous, FMap.get fs q' = some previous → file.mtime ≠ previous.mtime

/-- A raw call uses global freshness. A raw replay uses recorded-or-fresh timestamps. -/
def ProbeDerivation.TimestampCondition {m : CommandModel sig} {executor : Executor}
    {before head after returned} (d : ProbeDerivation m executor before head after returned) : Prop :=
  match ProbeDerivation.callFS d with
  | some fs => FreshPatch (ProbeDerivation.result d).patch fs before.fs
  | none => ReplayTimestamps (ProbeDerivation.appliedPatch d) (ProbeDerivation.result d).patch before.fs

/-- Executions satisfy timestamp side conditions and whole-map consistency at every prefix. -/
structure Operational {m : CommandModel sig} {h : Host sig} {executor : Executor}
    {prog : sig.Prog} {start : World sig} (pre : Prefix m h executor prog start) : Prop where
  timestamps : ∀ d ∈ pre.trace, ProbeDerivation.TimestampCondition d.probe
  consistentPrefixes : ∀ n, n ≤ pre.trace.length →
    TimestampConsistent (tracePaperRecords start (pre.trace.take n))

/-- Proof support for normalized occurrences, after the exact occurrence bridge. -/
theorem Operational.normalizedConsistentPrefixes {m : CommandModel sig} {h : Host sig}
    {executor : Executor} {prog : sig.Prog} {start : World sig}
    {pre : Prefix m h executor prog start} (operational : Operational pre)
    (n : Nat) (bound : n ≤ pre.trace.length) :
    TimestampCompatible (worldRecords start ++ (pre.trace.take n).flatMap StepDerivation.records) :=
  (tracePaperRecords_consistent_iff start (pre.trace.take n)).mp (operational.consistentPrefixes n bound)

/-- E.3's additional initial-cache condition chooses witnesses separately per run. -/
def InitialCacheConsistent {m : CommandModel sig} {h : Host sig} {executor : Executor}
    {prog : sig.Prog} {start : World sig} (pre : Prefix m h executor prog start) : Prop :=
  ∃ witnesses : WitnessMap sig, WitnessesFor m start.cache witnesses ∧
    TimestampConsistent (pre.paperRecords ∪ witnessPaperRecords witnesses)

/-- The source and target domain of E.12, before imposing program exit ordering. -/
structure AdmittedRun (m : CommandModel sig) (h : Host sig) (executor : Executor)
    (prog : sig.Prog) (start : World sig) where
  run : Run m h executor prog start
  operational : Operational run.toPrefix
  cacheConsistent : InitialCacheConsistent run.toPrefix

end
end IncrPP
end Incr
