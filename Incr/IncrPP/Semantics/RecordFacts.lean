import Incr.IncrPP.Semantics.Records

/-!
# Whole-map live record inventory facts

File-occurrence bridges support existing proofs. They do not identify the
whole-map E.3 collection with an implementation scan.
-/

namespace Incr.IncrPP

noncomputable section

variable {sig : Signature} {m : CommandModel sig} {h : Host sig}
  {executor : Executor} {prog : sig.Prog} {start : World sig}

theorem cachePaperRecords_occurrences (cache : Cache sig) (q : sig.Path) (file : File sig) :
    (q, file) ∈ recordOccurrences (cachePaperRecords cache) ↔ (q, file) ∈ cacheRecords cache := by
  simp only [recordOccurrences, cachePaperRecords, Set.mem_ofPred_eq, cacheRecords, List.mem_flatMap]
  constructor
  · rintro ⟨record, ⟨key, memo, present, rfl⟩, lookup⟩
    refine ⟨⟨key, memo⟩, ?_, (mem_patchRecords_iff_lookup memo.patch q file).mpr lookup⟩
    exact Multiset.mem_toList.mpr (Finmap.lookup_eq_some_iff.mp present)
  · rintro ⟨⟨key, memo⟩, present, member⟩
    refine ⟨memo.patch, ⟨key, memo, ?_, rfl⟩, (mem_patchRecords_iff_lookup memo.patch q file).mp member⟩
    exact Finmap.lookup_eq_some_iff.mpr (Multiset.mem_toList.mp present)

theorem witnessPaperRecords_occurrences (witnesses : WitnessMap sig) (q : sig.Path) (file : File sig) :
    (q, file) ∈ recordOccurrences (witnessPaperRecords witnesses) ↔ (q, file) ∈ witnessRecords witnesses := by
  simp only [recordOccurrences, witnessPaperRecords, Set.mem_ofPred_eq, witnessRecords, List.mem_flatMap]
  constructor
  · rintro ⟨record, ⟨key, witness, present, rfl⟩, lookup⟩
    refine ⟨⟨key, witness⟩, ?_, mem_fsRecords_of_get ?_⟩
    · exact Multiset.mem_toList.mpr (Finmap.lookup_eq_some_iff.mp present)
    · rw [get_recordOfFS, Option.map_eq_some_iff] at lookup
      obtain ⟨found, foundAt, equal⟩ := lookup
      cases Edit.write.inj equal
      exact foundAt
  · rintro ⟨⟨key, witness⟩, present, member⟩
    refine ⟨recordOfFS witness.fs, ⟨key, witness, ?_, rfl⟩, ?_⟩
    · exact Finmap.lookup_eq_some_iff.mpr (Multiset.mem_toList.mp present)
    · rw [get_recordOfFS, get_of_mem_fsRecords member]
      rfl

/-- Old implementation scans introduce no file value outside the base or patch. -/
theorem paper_scan_lookup_sources
    (entries : List (Sigma fun _ : sig.Path => Edit sig)) (fs : FS sig)
    {snapshot : FS sig} {q : sig.Path} {file : File sig}
    (member : snapshot ∈ entries.scanl (fun acc kv =>
      match kv.2 with
      | .write f => acc[kv.1 ↦ f]
      | .delete => acc ∖ kv.1) fs)
    (lookup : FMap.get snapshot q = some file) :
    FMap.get fs q = some file ∨ (⟨q, .write file⟩ : Sigma fun _ : sig.Path => Edit sig) ∈ entries := by
  induction entries generalizing fs with
  | nil =>
    simp only [List.scanl_nil, List.mem_singleton] at member
    subst snapshot
    exact Or.inl lookup
  | cons kv rest ih =>
    simp only [List.scanl_cons, List.mem_cons] at member
    rcases member with rfl | member
    · exact Or.inl lookup
    · rcases ih _ member with origin | inserted
      · cases kv with
        | mk key edit =>
          cases edit with
          | write newFile =>
            by_cases hq : q = key
            · subst key
              rw [FMap.get_set_self] at origin
              cases Option.some.inj origin
              exact Or.inr List.mem_cons_self
            · exact Or.inl (by simpa only [FMap.get_set_other hq] using origin)
          | delete =>
            by_cases hq : q = key
            · subst key
              simp only [FMap.get_erase_self] at origin
              contradiction
            · exact Or.inl (by simpa only [FMap.get_erase_of_ne hq] using origin)
      · exact Or.inr (List.mem_cons_of_mem _ inserted)

theorem paper_applicationRecords_sources {fs : FS sig} {patch : Patch sig}
    {q : sig.Path} {file : File sig} (member : (q, file) ∈ applicationRecords fs patch) :
    (q, file) ∈ fsRecords fs ∨ (q, file) ∈ patchRecords patch := by
  obtain ⟨snapshot, inScan, present⟩ := List.mem_flatMap.mp member
  rcases paper_scan_lookup_sources patch.entries.toList fs inScan (get_of_mem_fsRecords present) with base | write
  · exact Or.inl (mem_fsRecords_of_get base)
  · exact Or.inr (List.mem_filterMap.mpr ⟨⟨q, .write file⟩, write, rfl⟩)

theorem paper_applyPatch_sources {fs : FS sig} {patch : Patch sig}
    {q : sig.Path} {file : File sig} (present : FMap.get (applyPatch fs patch) q = some file) :
    FMap.get fs q = some file ∨ FMap.get patch q = some (.write file) := by
  cases edit : FMap.get patch q with
  | none => exact Or.inl (by simpa only [applyPatch_get_none edit] using present)
  | some e =>
    cases e with
    | delete => simp only [applyPatch_get_delete edit] at present; contradiction
    | write f =>
      rw [applyPatch_get_write edit] at present
      cases Option.some.inj present
      exact Or.inr rfl

/-- Live world records have the same file occurrences as the normalized support list. -/
theorem worldPaperRecords_occurrences (world : World sig) (q : sig.Path) (file : File sig) :
    (q, file) ∈ recordOccurrences (worldPaperRecords world) ↔ (q, file) ∈ worldRecords world := by
  simp only [worldPaperRecords, recordOccurrences_union, Set.mem_union,
    mem_recordOccurrences_fs_iff_mem_fsRecords, cachePaperRecords_occurrences,
    worldRecords, List.mem_append, List.mem_flatMap]
  constructor
  · rintro ((base | cache) | ⟨record, ⟨slot, sb, present, recordCase⟩, lookup⟩)
    · exact Or.inl (Or.inl base)
    · exact Or.inl (Or.inr cache)
    · apply Or.inr
      refine ⟨⟨slot, sb⟩, Multiset.mem_toList.mpr (Finmap.lookup_eq_some_iff.mp present), ?_⟩
      rcases recordCase with rfl | rfl
      · apply Or.inl
        apply mem_fsRecords_of_get
        rw [get_recordOfFS, Option.map_eq_some_iff] at lookup
        obtain ⟨f, hf, he⟩ := lookup
        cases Edit.write.inj he
        exact hf
      · exact Or.inr ((mem_patchRecords_iff_lookup sb.patch q file).mpr lookup)
  · rintro ((base | cache) | ⟨⟨slot, sb⟩, present, base | patch⟩)
    · exact Or.inl (Or.inl base)
    · exact Or.inl (Or.inr cache)
    · exact Or.inr ⟨recordOfFS sb.base,
        ⟨slot, sb, Finmap.lookup_eq_some_iff.mpr (Multiset.mem_toList.mp present), Or.inl rfl⟩,
        by rw [get_recordOfFS, get_of_mem_fsRecords base]; rfl⟩
    · exact Or.inr ⟨sb.patch,
        ⟨slot, sb, Finmap.lookup_eq_some_iff.mpr (Multiset.mem_toList.mp present), Or.inr rfl⟩,
        (mem_patchRecords_iff_lookup sb.patch q file).mp patch⟩

/-- Every live rule applies its retained actual patch to the selected filesystem. -/
theorem ProbeDerivation.applied_after {before : World sig} {head : Head sig}
    {after : World sig} {returned : Option Chunk}
    (probe : ProbeDerivation m executor before head after returned) :
    after.fs = applyPatch before.fs (ProbeDerivation.appliedPatch probe) := by
  cases executor <;> cases probe <;>
    simp_all [ProbeDerivation.appliedPatch, LiveDerivation.appliedPatch,
      VanillaDerivation.appliedPatch, closeWorld, standaloneWorld]

/-- Each application result is the after-world filesystem. -/
theorem StepDerivation.applicationPaperRecords_subset_after (d : StepDerivation m h executor prog) :
    d.applicationPaperRecords ⊆ worldPaperRecords d.after := by
  intro record member
  have same : record = recordOfFS (applyPatch d.selected.fs (ProbeDerivation.appliedPatch d.probe)) :=
    Set.mem_singleton_iff.mp member
  subst record
  rw [← ProbeDerivation.applied_after d.probe]
  exact Or.inl (Or.inl rfl)

/-- Live step collections and normalized lists have the same file occurrences. -/
theorem StepDerivation.paperRecords_occurrences (d : StepDerivation m h executor prog)
    (q : sig.Path) (file : File sig) :
    (q, file) ∈ recordOccurrences d.paperRecords ↔ (q, file) ∈ d.records := by
  simp only [StepDerivation.paperRecords, recordOccurrences_union, Set.mem_union,
    worldPaperRecords_occurrences, mem_recordOccurrences_patch, ← mem_patchRecords_iff_lookup,
    StepDerivation.records, List.mem_append, or_assoc]
  constructor
  · rintro (before | selected | after | result | ⟨record, ⟨fs, call, rfl⟩, lookup⟩ | applied | application)
    · exact Or.inl before
    · exact Or.inr (Or.inl selected)
    · exact Or.inr (Or.inr (Or.inl after))
    · exact Or.inr (Or.inr (Or.inr (Or.inl result)))
    · have atCall : FMap.get fs q = some file := by
        rw [get_recordOfFS, Option.map_eq_some_iff] at lookup
        obtain ⟨f, present, same⟩ := lookup
        cases Edit.write.inj same
        exact present
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [call]; exact mem_fsRecords_of_get atCall)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl applied)))))
    · obtain ⟨record, recorded, lookup⟩ := application
      have inAfter := d.applicationPaperRecords_subset_after recorded
      exact Or.inr (Or.inr (Or.inl ((worldPaperRecords_occurrences d.after q file).mp
        ⟨record, inAfter, lookup⟩)))
  · rintro (before | selected | after | result | call | applied | scan)
    · exact Or.inl before
    · exact Or.inr (Or.inl selected)
    · exact Or.inr (Or.inr (Or.inl after))
    · exact Or.inr (Or.inr (Or.inr (Or.inl result)))
    · cases callEq : ProbeDerivation.callFS d.probe with
      | none => simp [callEq] at call
      | some fs =>
        simp only [callEq] at call
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨recordOfFS fs, ⟨fs, callEq, rfl⟩,
          by rw [get_recordOfFS, get_of_mem_fsRecords call]; rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl applied)))))
    · rcases paper_applicationRecords_sources scan with inFS | inPatch
      · have inWorld : (q, file) ∈ worldRecords d.selected :=
          List.mem_append_left _ (List.mem_append_left _ inFS)
        exact Or.inr (Or.inl inWorld)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl inPatch)))))

/-- Initial-world and per-step occurrences agree for every finite trace. -/
theorem tracePaperRecords_occurrences (initial : World sig) (trace : Trace m h executor prog)
    (q : sig.Path) (file : File sig) :
    (q, file) ∈ recordOccurrences (tracePaperRecords initial trace) ↔
      (q, file) ∈ worldRecords initial ++ trace.flatMap StepDerivation.records := by
  simp only [tracePaperRecords, recordOccurrences_union, Set.mem_union,
    worldPaperRecords_occurrences, List.mem_append, List.mem_flatMap]
  constructor
  · rintro (initial | ⟨record, ⟨d, atStep, inStep⟩, lookup⟩)
    · exact Or.inl initial
    · exact Or.inr ⟨d, atStep, (d.paperRecords_occurrences q file).mp ⟨record, inStep, lookup⟩⟩
  · rintro (initial | ⟨d, atStep, inStep⟩)
    · exact Or.inl initial
    · obtain ⟨record, inStep, lookup⟩ := (d.paperRecords_occurrences q file).mpr inStep
      exact Or.inr ⟨record, ⟨d, atStep, inStep⟩, lookup⟩

theorem Prefix.paperRecords_occurrences (pre : Prefix m h executor prog start)
    (q : sig.Path) (file : File sig) :
    (q, file) ∈ recordOccurrences pre.paperRecords ↔ (q, file) ∈ pre.records :=
  tracePaperRecords_occurrences start pre.trace q file

theorem tracePaperRecords_consistent_iff (initial : World sig) (trace : Trace m h executor prog) :
    TimestampConsistent (tracePaperRecords initial trace) ↔
      TimestampCompatible (worldRecords initial ++ trace.flatMap StepDerivation.records) :=
  timestampConsistent_iff_normalized _ _ (tracePaperRecords_occurrences initial trace)

theorem worldPaperRecords_witness_consistent_iff (world : World sig) (witnesses : WitnessMap sig) :
    TimestampConsistent (worldPaperRecords world ∪ witnessPaperRecords witnesses) ↔
      TimestampCompatible (worldRecords world ++ witnessRecords witnesses) := by
  apply timestampConsistent_iff_normalized
  intro q file
  rw [recordOccurrences_union, Set.mem_union, List.mem_append,
    worldPaperRecords_occurrences, witnessPaperRecords_occurrences]

theorem two_filesystems_consistent_iff (left right : FS sig) :
    TimestampConsistent ({recordOfFS left} ∪ {recordOfFS right}) ↔
      TimestampCompatible (fsRecords left ++ fsRecords right) := by
  apply timestampConsistent_iff_normalized
  intro q file
  rw [recordOccurrences_union, Set.mem_union, List.mem_append,
    mem_recordOccurrences_fs_iff_mem_fsRecords, mem_recordOccurrences_fs_iff_mem_fsRecords]

theorem Prefix.paperRecords_witness_consistent_iff (pre : Prefix m h executor prog start)
    (witnesses : WitnessMap sig) :
    TimestampConsistent (pre.paperRecords ∪ witnessPaperRecords witnesses) ↔
      TimestampCompatible (pre.records ++ witnessRecords witnesses) := by
  apply timestampConsistent_iff_normalized
  intro q file
  rw [recordOccurrences_union, Set.mem_union, List.mem_append,
    pre.paperRecords_occurrences, witnessPaperRecords_occurrences]

end
end IncrPP
end Incr
