import Incr.Incr.Support.PaperRecordFacts

/-!
# Conditions on recorded executions (`def:paper-timestamps`, timestamp consistency)

This file separates raw transitions from execution conditions. Operational
consistency uses the `def:paper-timestamps` whole-map collection;
normalized file occurrences remain available for proof transport.
-/

open Incr
namespace Incr.Incr

noncomputable section

variable {sig : Signature}

/-- Every actual command call is fresh against its call and live filesystems.
A replay contributes no call-freshness obligation. -/
def FreshCalls {m : CommandModel sig} {h : Host sig} {executor : Executor} {prog : sig.Prog}
    (trace : Trace m h executor prog) : Prop :=
  ∀ d ∈ trace, ProbeDerivation.Fresh d.probe

/-- The two shared execution conditions, separate from the raw transition rules. -/
structure Operational {m : CommandModel sig} {h : Host sig} {executor : Executor}
    {prog : sig.Prog} {start : World sig} (pre : Prefix m h executor prog start) : Prop where
  fresh : FreshCalls pre.trace
  timestamps : TimestampConsistent pre.paperRecords

/-- Proof support: actual map-level consistency implies normalized consistency. -/
theorem Operational.normalizedTimestamps {m : CommandModel sig} {h : Host sig} {executor : Executor}
    {prog : sig.Prog} {start : World sig} {pre : Prefix m h executor prog start}
    (operational : Operational pre) : TimestampCompatible pre.records :=
  pre.paperRecords_consistent_iff.mp operational.timestamps

/-- The `def:paper-timestamps` general condition for a finite list of externally
specified caches. -/
def ConsistentWithCaches (m : CommandModel sig) (records : RecordCollection sig)
    (caches : List (Cache sig)) : Prop :=
  ∃ witnesses : List (WitnessMap sig),
    List.Forall₂ (WitnessesFor m) caches witnesses ∧
      TimestampConsistent
        (records ∪ specifiedCachePaperRecords caches ∪ specifiedWitnessPaperRecords witnesses)

/-- A whole-map prefix and the old normalized lists have the same file occurrences. -/
theorem prefix_specified_consistent_iff {m : CommandModel sig} {h : Host sig} {executor : Executor}
    {prog : sig.Prog} {start : World sig} (pre : Prefix m h executor prog start)
    (caches : List (Cache sig)) (witnesses : List (WitnessMap sig)) :
    TimestampConsistent (pre.paperRecords ∪ specifiedCachePaperRecords caches ∪
      specifiedWitnessPaperRecords witnesses) ↔
      TimestampCompatible (pre.records ++ (caches.flatMap cacheRecords ++ witnesses.flatMap witnessRecords)) := by
  apply timestampConsistent_iff_normalized
  intro q file
  simp only [recordOccurrences_union, Set.mem_union, List.mem_append,
    pre.paperRecords_occurrences, specifiedCachePaperRecords_occurrences,
    specifiedWitnessPaperRecords_occurrences, or_assoc]

/-- Initial-cache witnesses are existential separately for each run. -/
def InitialCacheConsistent {m : CommandModel sig} {h : Host sig} {executor : Executor}
    {prog : sig.Prog} {start : World sig} (pre : Prefix m h executor prog start) : Prop :=
  ConsistentWithCaches m pre.paperRecords [start.cache]

/-- A paper-admitted terminating run. Isolation remains a program assumption. -/
structure AdmittedRun (m : CommandModel sig) (h : Host sig) (executor : Executor)
    (prog : sig.Prog) (start : World sig) where
  run : Run m h executor prog start
  operational : Operational run.toPrefix
  cacheConsistent : InitialCacheConsistent run.toPrefix

end
end Incr.Incr
