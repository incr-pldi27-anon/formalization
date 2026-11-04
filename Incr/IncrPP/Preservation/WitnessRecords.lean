import Incr.IncrPP.Bisimulation.Statements

/-!
# Actual selected records and local witness provenance

The selected world's newly initialized sandboxes copy the actual current
filesystem. No future probe or joint consistency among current memo witnesses
is assumed.
-/

namespace Incr.IncrPP

noncomputable section

variable {sig : Signature} {m : CommandModel sig} {h : Host sig}
  {executor : Executor} {prog : sig.Prog} {start : World sig}

/-- A permitted selection adds no new file record beyond its actual prefix. -/
theorem selected_world_records (host : HostWellFormed m h)
    (pre : Prefix m h executor prog start) (operational : Operational pre)
    (selection : Selection sig) (world : World sig) (allowed : h.select prog pre.final selection world) :
    ∀ record ∈ worldRecords world, record ∈ pre.records := by
  have discipline := host.selectionDiscipline executor prog start pre operational selection world allowed
  intro record member
  have fsEq := discipline.1
  have cacheEq := discipline.2.2.1
  cases initializes : selection.init with
  | none =>
    have same : worldRecords world = worldRecords pre.final := by
      have allocation := discipline.2.2.2.1
      simp only [initializes] at allocation
      simp only [worldRecords, fsEq, cacheEq, allocation.1]
    rw [same] at member
    exact pre.final_world_records record member
  | some init =>
    have allocation := discipline.2.2.2.1
    simp only [initializes] at allocation
    have sandboxEq : world.sandbox = initialSandboxes init pre.final.fs := allocation.2.2.2.2
    simp only [worldRecords, List.mem_append] at member
    rcases member with (fsMember | cacheMember) | sandboxMember
    · apply pre.final_world_records
      simp only [worldRecords, List.mem_append]
      left; left
      simpa [fsEq] using fsMember
    · apply pre.final_world_records
      simp only [worldRecords, List.mem_append]
      left; right
      simpa [cacheEq] using cacheMember
    · obtain ⟨kv, kvMember, fromEntry⟩ := List.mem_flatMap.mp sandboxMember
      have lookup : FMap.get world.sandbox kv.1 = some kv.2 := by
        exact Finmap.lookup_eq_some_iff.mpr (Multiset.mem_toList.mp kvMember)
      rw [sandboxEq] at lookup
      have initial := initialSandboxes_value init pre.final.fs lookup
      have fromFS : record ∈ fsRecords pre.final.fs := by
        have emptyPatch : patchRecords (∅ : Patch sig) = [] := by
          apply List.eq_nil_iff_forall_not_mem.mpr
          intro item member
          unfold patchRecords at member
          obtain ⟨entry, inEntries, _⟩ := List.mem_filterMap.mp member
          have inMap : entry.1 ∈ (∅ : Patch sig) := by
            rw [Finmap.mem_iff]
            exact ⟨entry.2, Finmap.lookup_eq_some_iff.mpr (Multiset.mem_toList.mp inEntries)⟩
          exact Finmap.notMem_empty inMap
        simpa only [initial, Sandbox.initial, emptyPatch, List.append_nil] using fromEntry
      apply pre.final_world_records
      simp only [worldRecords, List.mem_append]
      exact Or.inl (Or.inl fromFS)

/-- Boundary records are already represented in the admitted endpoint records. -/
theorem Boundary.records_subset (host : HostWellFormed m h)
    (pre : Prefix m h executor prog start) (operational : Operational pre) (b : Boundary pre) :
    ∀ record ∈ b.records, record ∈ pre.records := by
  intro record member
  cases b with
  | final => exact member
  | selected selection world allowed =>
    simp only [Boundary.records, List.mem_append] at member
    rcases member with old | selected
    · exact old
    · exact selected_world_records host pre operational selection world allowed record selected

/-- A provenance witness's files are among actual boundary records or fixed initial witness records. -/
theorem WitnessProvenance.records_subset {initial : WitnessMap sig} {records : Records sig} {fs : FS sig}
    (provenance : WitnessProvenance initial records fs) :
    ∀ record ∈ fsRecords fs, record ∈ records ++ witnessRecords initial := by
  intro record member
  rcases record with ⟨q, file⟩
  have lookup := get_of_mem_fsRecords member
  rcases provenance with ⟨key, witness, witnessAt, fsEq⟩ | copied
  · apply List.mem_append_right
    unfold witnessRecords
    apply List.mem_flatMap.mpr
    refine ⟨⟨key, witness⟩, ?_, ?_⟩
    · exact Multiset.mem_toList.mpr (Finmap.lookup_eq_some_iff.mp witnessAt)
    · simpa only [fsEq] using member
  · exact List.mem_append_left _ (copied q file lookup)

/-- Provenance and admitted endpoint consistency imply the full selected-boundary consistency. -/
theorem WitnessProvenance.consistent_at_boundary (host : HostWellFormed m h)
    (pre : Prefix m h executor prog start) (operational : Operational pre) (b : Boundary pre)
    (initial : WitnessMap sig) (consistent : TimestampCompatible (pre.records ++ witnessRecords initial))
    (fs : FS sig) (provenance : WitnessProvenance initial b.records fs) :
    TimestampCompatible (fsRecords fs ++ b.records ++ witnessRecords initial) := by
  apply TimestampCompatible.mono ?_ consistent
  intro record member
  simp only [List.mem_append] at member ⊢
  rcases member with (fromWitness | fromBoundary) | fromInitial
  · have origin := provenance.records_subset record fromWitness
    rcases List.mem_append.mp origin with actual | fixed
    · exact Or.inl (Boundary.records_subset host pre operational b record actual)
    · exact Or.inr fixed
  · exact Or.inl (Boundary.records_subset host pre operational b record fromBoundary)
  · exact Or.inr fromInitial

/-- E.10 uses whole-map consistency, derived through occurrence support only. -/
theorem RecordedWitnessProvenance.consistent_at_boundary (host : HostWellFormed m h)
    (pre : Prefix m h executor prog start) (operational : Operational pre) (b : Boundary pre)
    (initial : WitnessMap sig)
    (consistent : TimestampConsistent (pre.paperRecords ∪ witnessPaperRecords initial))
    (fs : FS sig) (provenance : RecordedWitnessProvenance initial b.paperRecords fs) :
    TimestampConsistent ({recordOfFS fs} ∪ b.paperRecords ∪ witnessPaperRecords initial) := by
  apply (b.paperRecords_witness_consistent_iff initial fs).mpr
  exact WitnessProvenance.consistent_at_boundary host pre operational b initial
    ((pre.paperRecords_witness_consistent_iff initial).mp consistent) fs
    ((recordedWitnessProvenance_iff_normalized initial _ _ b.paperRecords_occurrences fs).mp provenance)

end
end IncrPP
end Incr
