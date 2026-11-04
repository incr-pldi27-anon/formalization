import Incr.IncrPP.WellFormedness.Host
import Incr.IncrPP.WellFormedness.ExitOrder

/-!
# Prefix endpoints and permitted selections

A boundary retains either the endpoint or one actual host selection. It
never assumes a subsequent probe judgment. A pending initialization has
index `pre.trace.length`; its snapshot is the current pre-selection state.
-/
namespace Incr.IncrPP

open Incr
noncomputable section
variable {sig : Signature} {m : CommandModel sig} {h : Host sig}
  {executor : Executor} {prog : sig.Prog} {start : World sig}

inductive Boundary (pre : Prefix m h executor prog start) where
  | final
  | selected (selection : Selection sig) (world : World sig)
      (allowed : h.select prog pre.final selection world)

def Boundary.world {pre : Prefix m h executor prog start} : Boundary pre → World sig
  | .final => pre.final
  | .selected _ world _ => world

def Boundary.selection? {pre : Prefix m h executor prog start} : Boundary pre → Option (Selection sig)
  | .final => none
  | .selected selection _ _ => some selection

/-- Recorded and pending pipeline entries, with actual initialization data. -/
def Boundary.entry {pre : Prefix m h executor prog start} (b : Boundary pre) (entry : Nat) :
    Option (FS sig × PipelineInit sig) :=
  if entry = pre.trace.length then
    b.selection?.bind fun selection => selection.init.map fun init => (pre.final.fs, init)
  else
    ((pre.trace)[entry]?).bind fun d => d.selection.init.map fun init => (d.before.fs, init)

def Boundary.currentEntry {pre : Prefix m h executor prog start} (b : Boundary pre) : Option Nat :=
  match b.selection?.bind (·.init) with
  | some _ => some pre.trace.length
  | none => (latestPipeline pre.trace).map Prod.fst

/-- Pending initialization contributes all assigned slots without any future step. -/
def Boundary.componentDomain {pre : Prefix m h executor prog start} (b : Boundary pre) : Set Component :=
  Incr.IncrPP.componentDomain pre.trace ∪ { k | ∃ init slot,
    (b.selection?.bind (·.init)) = some init ∧ slot < init.probes.length ∧
      k = .pipeline pre.trace.length slot }

def Boundary.livePipeline {pre : Prefix m h executor prog start} (b : Boundary pre)
    (entry slot : Nat) : Prop :=
  b.currentEntry = some entry ∧ .pipeline entry slot ∈ b.componentDomain ∧
    closingPositions pre.trace (.pipeline entry slot) = []

def Boundary.unclosedSlots {pre : Prefix m h executor prog start} (b : Boundary pre) : Set Nat :=
  { slot | ∃ entry, b.livePipeline entry slot }

/-- Assignment is read from initialization, not guessed from a future call. -/
def Boundary.assigned {pre : Prefix m h executor prog start} (b : Boundary pre)
    (entry slot : Nat) (p : sig.Probe) : Prop :=
  ∃ fs init, b.entry entry = some (fs, init) ∧ init.probes[slot]? = some p

/-- Normalized proof support for the boundary's file occurrences. -/
def Boundary.records {pre : Prefix m h executor prog start} (b : Boundary pre) : Records sig :=
  match b with
  | .final => pre.records
  | .selected _ world _ => pre.records ++ worldRecords world

/-- E.3 whole-map records at an endpoint or actual permitted selection. -/
def Boundary.paperRecords {pre : Prefix m h executor prog start} (b : Boundary pre) : RecordCollection sig :=
  match b with
  | .final => pre.paperRecords
  | .selected _ world _ => pre.selectedPaperRecords world

/-- The boundary bridge concerns file occurrences, not equality of map inventories. -/
theorem Boundary.paperRecords_occurrences {pre : Prefix m h executor prog start} (b : Boundary pre)
    (q : sig.Path) (file : File sig) :
    (q, file) ∈ recordOccurrences b.paperRecords ↔ (q, file) ∈ b.records := by
  cases b with
  | final => exact pre.paperRecords_occurrences q file
  | selected selection world allowed =>
    change (q, file) ∈ recordOccurrences (pre.paperRecords ∪ worldPaperRecords world) ↔
      (q, file) ∈ pre.records ++ worldRecords world
    rw [recordOccurrences_union, Set.mem_union, List.mem_append,
      pre.paperRecords_occurrences, worldPaperRecords_occurrences]

/-- The full E.10 consistency package has a normalized proof-support view. -/
theorem Boundary.paperRecords_witness_consistent_iff {pre : Prefix m h executor prog start}
    (b : Boundary pre) (initial : WitnessMap sig) (fs : FS sig) :
    TimestampConsistent ({recordOfFS fs} ∪ b.paperRecords ∪ witnessPaperRecords initial) ↔
      TimestampCompatible (fsRecords fs ++ b.records ++ witnessRecords initial) := by
  apply timestampConsistent_iff_normalized
  intro q file
  rw [recordOccurrences_union, recordOccurrences_union, Set.mem_union, Set.mem_union,
    List.mem_append, List.mem_append, mem_recordOccurrences_fs_iff_mem_fsRecords,
    b.paperRecords_occurrences, witnessPaperRecords_occurrences]

/-- Open judgments of a component, in their original step order. -/
def openSteps (trace : Trace m h executor prog) (k : Component) : Trace m h executor prog :=
  (componentSteps trace k).filter fun d => (ProbeDerivation.input d.probe).flag == .open

/-- Partial list concatenation retains the open-left domain, including at empty history. -/
def concatenate (chunks : List Chunk) : Option Chunk :=
  chunks.foldlM (fun previous next =>
    if flag : previous.flag = .open then some (Chunk.concat previous next flag) else none)
    Chunk.emptyOpen

def historyPatch (steps : Trace m h executor prog) : Patch sig :=
  steps.foldl (fun patch d => patch ⊎ (ProbeDerivation.result d.probe).patch) ∅

def historyWrites (steps : Trace m h executor prog) : Set sig.Path :=
  { q | ∃ d ∈ steps, q ∈ FMap.dom (ProbeDerivation.result d.probe).patch }

def historyReads (steps : Trace m h executor prog) : Reads sig :=
  (steps.mapIdx fun j d => (ProbeDerivation.result d.probe).reads ↾
    (historyWrites (steps.take j))ᶜ).foldl FMap.merge ∅

def historyWriteDeps (steps : Trace m h executor prog) : Writes sig :=
  (steps.mapIdx fun j d => (ProbeDerivation.result d.probe).writes ↾
    (historyWrites (steps.take j))ᶜ).foldl FMap.merge ∅

/-- The first actual call environment, with no fabricated default. -/
def FirstEnvironment (trace : Trace m h executor prog) (k : Component) (env : Env sig) : Prop :=
  ∃ first, (componentSteps trace k).head? = some first ∧ first.selected.env = env

end
end IncrPP
end Incr
