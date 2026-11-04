import Incr.Incr.Semantics.NormalizedRecords
import Incr.Model.Records

/-!
# Whole-map records of sandbox-mode executions

RC1 preserves the `def:paper-timestamps` filesystem and patch collection. These
definitions are
separate from the normalized file occurrences used by existing proofs.
-/

open Incr
namespace Incr.Incr

noncomputable section

variable {sig : Signature}

/-- Every patch in an actual cache is a whole recorded map. -/
def cachePaperRecords (cache : Cache sig) : RecordCollection sig :=
  {record | ∃ key memo, FMap.get cache key = some memo ∧ record = memo.patch}

/-- Every selected historical witness contributes its whole filesystem. -/
def witnessPaperRecords (witnesses : WitnessMap sig) : RecordCollection sig :=
  {record | ∃ key witness, FMap.get witnesses key = some witness ∧ record = recordOfFS witness.fs}

/-- The whole patches of the externally specified caches. -/
def specifiedCachePaperRecords (caches : List (Cache sig)) : RecordCollection sig :=
  {record | ∃ cache ∈ caches, record ∈ cachePaperRecords cache}

/-- The whole witness filesystems selected for specified caches. -/
def specifiedWitnessPaperRecords (witnesses : List (WitnessMap sig)) : RecordCollection sig :=
  {record | ∃ chosen ∈ witnesses, record ∈ witnessPaperRecords chosen}

/-- The `def:paper-timestamps` records hold the live filesystem, cache patches,
and each sandbox's base, patch, and sandbox view. Empty maps are retained as
members. -/
def worldPaperRecords (world : World sig) : RecordCollection sig :=
  {recordOfFS world.fs} ∪ cachePaperRecords world.cache ∪
    {record | ∃ slot sb, FMap.get world.sandbox slot = some sb ∧
      (record = recordOfFS sb.base ∨ record = sb.patch ∨ record = recordOfFS sb.view)}

/-- The filesystem argument of an actual executing call. Hits contribute none. -/
def StepDerivation.callPaperRecords {m : CommandModel sig} {h : Host sig}
    {executor : Executor} {prog : sig.Prog} (d : StepDerivation m h executor prog) : RecordCollection sig :=
  {record | ∃ fs, ProbeDerivation.callFS d.probe = some fs ∧ record = recordOfFS fs}

/-- A sandbox pipeline call evaluates its captured base plus accumulated patch.
Standalone and vanilla calls use the live filesystem directly; hits make no call. -/
def StepDerivation.sandboxApplication {m : CommandModel sig} {h : Host sig}
    {executor : Executor} {prog : sig.Prog} (d : StepDerivation m h executor prog) : Option (FS sig) :=
  match executor, d.selection.head with
  | .incr, .pipeline _ _ => ProbeDerivation.callFS d.probe
  | _, _ => none

/-- The whole outputs of actual semantic sandbox-view and live-commit applications.
No partial-entry implementation scan is part of this collection. -/
def StepDerivation.applicationPaperRecords {m : CommandModel sig} {h : Host sig}
    {executor : Executor} {prog : sig.Prog} (d : StepDerivation m h executor prog) : RecordCollection sig :=
  {record | ∃ fs, d.sandboxApplication = some fs ∧ record = recordOfFS fs} ∪
    {record | ∃ patch, d.livePatch = some patch ∧ record = recordOfFS (applyPatch d.selected.fs patch)}

/-- The `def:paper-timestamps` categories for one actual recorded host/probe
derivation. -/
def StepDerivation.paperRecords {m : CommandModel sig} {h : Host sig}
    {executor : Executor} {prog : sig.Prog} (d : StepDerivation m h executor prog) : RecordCollection sig :=
  worldPaperRecords d.before ∪ worldPaperRecords d.selected ∪ worldPaperRecords d.after ∪
    {(ProbeDerivation.result d.probe).patch} ∪ d.callPaperRecords ∪ d.applicationPaperRecords

/-- The initial world and every actual step, with whole maps retained. -/
def Prefix.paperRecords {m : CommandModel sig} {h : Host sig} {executor : Executor}
    {prog : sig.Prog} {start : World sig} (pre : Prefix m h executor prog start) : RecordCollection sig :=
  worldPaperRecords start ∪ {record | ∃ d ∈ pre.trace, record ∈ d.paperRecords}

/-- An allowed selection contributes its world even without a later probe. -/
def Prefix.selectedPaperRecords {m : CommandModel sig} {h : Host sig} {executor : Executor}
    {prog : sig.Prog} {start : World sig} (pre : Prefix m h executor prog start)
    (selected : World sig) : RecordCollection sig := pre.paperRecords ∪ worldPaperRecords selected

end
end Incr.Incr
