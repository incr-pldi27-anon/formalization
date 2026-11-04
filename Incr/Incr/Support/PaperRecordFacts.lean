import Incr.Incr.Semantics.Records

/-!
# Whole-map record inventory facts

These facts check the independently named `def:paper-timestamps` categories
without replacing
public admission by flattened file records.
-/

open Incr
namespace Incr.Incr

noncomputable section

variable {sig : Signature} {m : CommandModel sig} {h : Host sig}
  {executor : Executor} {prog : sig.Prog} {start : World sig}

@[simp] theorem mem_cachePaperRecords {cache : Cache sig} {record : RecordMap sig} :
    record ∈ cachePaperRecords cache ↔
      ∃ key memo, FMap.get cache key = some memo ∧ record = memo.patch := Iff.rfl

@[simp] theorem mem_witnessPaperRecords {witnesses : WitnessMap sig} {record : RecordMap sig} :
    record ∈ witnessPaperRecords witnesses ↔
      ∃ key witness, FMap.get witnesses key = some witness ∧ record = recordOfFS witness.fs := Iff.rfl

/-- Two explicitly recorded filesystems support the old local file-level proof. -/
theorem two_filesystems_consistent_iff (left right : FS sig) :
    TimestampConsistent ({recordOfFS left} ∪ {recordOfFS right}) ↔
      TimestampCompatible (fsRecords left ++ fsRecords right) := by
  apply timestampConsistent_iff_normalized
  intro q file
  rw [recordOccurrences_union, Set.mem_union, List.mem_append,
    mem_recordOccurrences_fs_iff_mem_fsRecords, mem_recordOccurrences_fs_iff_mem_fsRecords]

/-- The cache's derived file occurrences match the previous proof inventory. -/
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

/-- Witness file occurrences match the previous proof inventory. -/
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

/-- The specified-cache collection has the same derived file occurrences. -/
theorem specifiedCachePaperRecords_occurrences (caches : List (Cache sig)) (q : sig.Path) (file : File sig) :
    (q, file) ∈ recordOccurrences (specifiedCachePaperRecords caches) ↔
      (q, file) ∈ caches.flatMap cacheRecords := by
  simp only [recordOccurrences, specifiedCachePaperRecords, Set.mem_ofPred_eq, List.mem_flatMap]
  constructor
  · rintro ⟨record, ⟨cache, inCaches, inCache⟩, lookup⟩
    exact ⟨cache, inCaches, (cachePaperRecords_occurrences cache q file).mp ⟨record, inCache, lookup⟩⟩
  · rintro ⟨cache, inCaches, member⟩
    obtain ⟨record, inCache, lookup⟩ := (cachePaperRecords_occurrences cache q file).mpr member
    exact ⟨record, ⟨cache, inCaches, inCache⟩, lookup⟩

/-- The specified-witness collection has the same derived file occurrences. -/
theorem specifiedWitnessPaperRecords_occurrences (witnesses : List (WitnessMap sig)) (q : sig.Path) (file : File sig) :
    (q, file) ∈ recordOccurrences (specifiedWitnessPaperRecords witnesses) ↔
      (q, file) ∈ witnesses.flatMap witnessRecords := by
  simp only [recordOccurrences, specifiedWitnessPaperRecords, Set.mem_ofPred_eq, List.mem_flatMap]
  constructor
  · rintro ⟨record, ⟨chosen, inChoices, inChosen⟩, lookup⟩
    exact ⟨chosen, inChoices, (witnessPaperRecords_occurrences chosen q file).mp ⟨record, inChosen, lookup⟩⟩
  · rintro ⟨chosen, inChoices, member⟩
    obtain ⟨record, inChosen, lookup⟩ := (witnessPaperRecords_occurrences chosen q file).mpr member
    exact ⟨record, ⟨chosen, inChoices, inChosen⟩, lookup⟩

/-- Every file in an old implementation scan comes from its base or patch. -/
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

/-- Scan file occurrences belong to the existing base or the whole patch. -/
theorem paper_applicationRecords_sources {fs : FS sig} {patch : Patch sig}
    {q : sig.Path} {file : File sig} (member : (q, file) ∈ applicationRecords fs patch) :
    (q, file) ∈ fsRecords fs ∨ (q, file) ∈ patchRecords patch := by
  obtain ⟨snapshot, inScan, present⟩ := List.mem_flatMap.mp member
  rcases paper_scan_lookup_sources patch.entries.toList fs inScan (get_of_mem_fsRecords present) with base | write
  · exact Or.inl (mem_fsRecords_of_get base)
  · exact Or.inr (List.mem_filterMap.mpr ⟨⟨q, .write file⟩, write, rfl⟩)

/-- A semantic patch output contains only same-path base or patch records. -/
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

/-- Whole `def:paper-timestamps` world maps and the old proof inventory have the
same file occurrences. -/
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
      rcases recordCase with rfl | rfl | rfl
      · exact Or.inl (Or.inl (mem_fsRecords_of_get (by
          rw [get_recordOfFS, Option.map_eq_some_iff] at lookup
          obtain ⟨f, hf, he⟩ := lookup
          cases Edit.write.inj he
          exact hf)))
      · exact Or.inl (Or.inr ((mem_patchRecords_iff_lookup sb.patch q file).mpr lookup))
      · rcases paper_applyPatch_sources (by
          rw [get_recordOfFS, Option.map_eq_some_iff] at lookup
          obtain ⟨f, hf, he⟩ := lookup
          cases Edit.write.inj he
          exact hf) with base | patch
        · exact Or.inl (Or.inl (mem_fsRecords_of_get base))
        · exact Or.inl (Or.inr ((mem_patchRecords_iff_lookup sb.patch q file).mpr patch))
  · rintro ((base | cache) | ⟨⟨slot, sb⟩, present, (base | patch) | scan⟩)
    · exact Or.inl (Or.inl base)
    · exact Or.inl (Or.inr cache)
    · exact Or.inr ⟨recordOfFS sb.base, ⟨slot, sb, Finmap.lookup_eq_some_iff.mpr (Multiset.mem_toList.mp present), Or.inl rfl⟩,
        by rw [get_recordOfFS, get_of_mem_fsRecords base]; rfl⟩
    · exact Or.inr ⟨sb.patch, ⟨slot, sb, Finmap.lookup_eq_some_iff.mpr (Multiset.mem_toList.mp present), Or.inr (Or.inl rfl)⟩,
        (mem_patchRecords_iff_lookup sb.patch q file).mp patch⟩
    · rcases paper_applicationRecords_sources scan with base | patch
      · exact Or.inr ⟨recordOfFS sb.base, ⟨slot, sb, Finmap.lookup_eq_some_iff.mpr (Multiset.mem_toList.mp present), Or.inl rfl⟩,
          by rw [get_recordOfFS, get_of_mem_fsRecords base]; rfl⟩
      · exact Or.inr ⟨sb.patch, ⟨slot, sb, Finmap.lookup_eq_some_iff.mpr (Multiset.mem_toList.mp present), Or.inr (Or.inl rfl)⟩,
          (mem_patchRecords_iff_lookup sb.patch q file).mp patch⟩

/-- A sandbox patch is represented by the selected world's old file inventory. -/
theorem sandbox_patch_mem_worldRecords {world : World sig} {slot : Nat} {sb : Sandbox sig}
    (present : FMap.get world.sandbox slot = some sb) {q : sig.Path} {file : File sig}
    (member : (q, file) ∈ patchRecords sb.patch) : (q, file) ∈ worldRecords world := by
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨⟨slot, sb⟩, Multiset.mem_toList.mpr (Finmap.lookup_eq_some_iff.mp present), ?_⟩
  exact List.mem_append_left _ (List.mem_append_right _ member)

/-- Merging patches adds no file value except one from an input patch. -/
theorem paper_merge_patch_sources {left right : Patch sig} {q : sig.Path} {file : File sig}
    (member : (q, file) ∈ patchRecords (left ⊎ right)) :
    (q, file) ∈ patchRecords left ∨ (q, file) ∈ patchRecords right := by
  have lookup := (mem_patchRecords_iff_lookup (left ⊎ right) q file).mp member
  rw [FMap.get_merge_elim] at lookup
  cases rightGet : FMap.get right q with
  | none =>
    exact Or.inl ((mem_patchRecords_iff_lookup left q file).mpr (by simpa [rightGet] using lookup))
  | some edit =>
    have same : edit = .write file := by simpa [rightGet] using lookup
    subst edit
    exact Or.inr ((mem_patchRecords_iff_lookup right q file).mpr rightGet)

/-- An applied sandbox patch draws its files from the selected world or result. -/
theorem IncrDerivation.livePatch_record_sources {before : World sig} {head : Head sig}
    {after : World sig} {returned : Option Chunk}
    (probe : IncrDerivation m before head after returned) {patch : Patch sig}
    (chosen : probe.livePatch = some patch) {q : sig.Path} {file : File sig}
    (member : (q, file) ∈ patchRecords patch) :
    (q, file) ∈ worldRecords before ∨ (q, file) ∈ patchRecords probe.result.patch := by
  cases probe <;> simp only [IncrDerivation.livePatch, IncrDerivation.result] at chosen ⊢
  all_goals try contradiction
  all_goals cases chosen
  all_goals first
    | exact Or.inr member
    | (rcases paper_merge_patch_sources member with old | new
       · exact Or.inl (sandbox_patch_mem_worldRecords (by assumption) old)
       · exact Or.inr new)

/-- The actual applied patch's file values occur in the selected world or result. -/
theorem StepDerivation.livePatch_record_sources (d : StepDerivation m h executor prog)
    {patch : Patch sig} (chosen : d.livePatch = some patch) {q : sig.Path} {file : File sig}
    (member : (q, file) ∈ patchRecords patch) :
    (q, file) ∈ worldRecords d.selected ∨ (q, file) ∈ patchRecords (ProbeDerivation.result d.probe).patch := by
  cases executor with
  | incr => exact IncrDerivation.livePatch_record_sources d.probe chosen member
  | vanilla =>
    have same : (VanillaDerivation.result d.probe).patch = patch := Option.some.inj chosen
    exact Or.inr (by simpa only [ProbeDerivation.result, same] using member)

/-- A sandbox application output is exactly an actual call filesystem. -/
theorem StepDerivation.sandboxApplication_callFS (d : StepDerivation m h executor prog)
    {fs : FS sig} (chosen : d.sandboxApplication = some fs) :
    ProbeDerivation.callFS d.probe = some fs := by
  unfold StepDerivation.sandboxApplication at chosen
  split at chosen <;> simp_all

/-- The whole-map step inventory and the old proof inventory have identical file occurrences. -/
theorem StepDerivation.paperRecords_occurrences (d : StepDerivation m h executor prog)
    (q : sig.Path) (file : File sig) :
    (q, file) ∈ recordOccurrences d.paperRecords ↔ (q, file) ∈ d.records := by
  simp only [StepDerivation.paperRecords, StepDerivation.applicationPaperRecords,
    recordOccurrences_union, Set.mem_union,
    worldPaperRecords_occurrences, mem_recordOccurrences_patch, ← mem_patchRecords_iff_lookup,
    StepDerivation.records, List.mem_append, or_assoc]
  constructor
  · rintro (before | selected | after | result | ⟨record, ⟨fs, call, rfl⟩, lookup⟩ |
      ⟨record, ⟨fs, chosen, rfl⟩, lookup⟩ | ⟨record, ⟨patch, chosen, rfl⟩, lookup⟩)
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
    · have call := d.sandboxApplication_callFS chosen
      have atCall : FMap.get fs q = some file := by
        rw [get_recordOfFS, Option.map_eq_some_iff] at lookup
        obtain ⟨f, present, same⟩ := lookup
        cases Edit.write.inj same
        exact present
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [call]; exact mem_fsRecords_of_get atCall)))))
    · rw [get_recordOfFS, Option.map_eq_some_iff] at lookup
      obtain ⟨f, present, same⟩ := lookup
      cases Edit.write.inj same
      rcases paper_applyPatch_sources present with inFS | inPatch
      · have inWorld : (q, file) ∈ worldRecords d.selected :=
          List.mem_append_left _ (List.mem_append_left _ (mem_fsRecords_of_get inFS))
        exact Or.inr (Or.inl inWorld)
      · have member := (mem_patchRecords_iff_lookup patch q file).mpr inPatch
        rcases d.livePatch_record_sources chosen member with inWorld | inResult
        · exact Or.inr (Or.inl inWorld)
        · exact Or.inr (Or.inr (Or.inr (Or.inl inResult)))
  · rintro (before | selected | after | result | call | applied)
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
    · cases patchEq : d.livePatch with
      | none => simp [patchEq] at applied
      | some patch =>
        simp only [patchEq, List.mem_append] at applied
        rcases applied with patchMember | scanMember
        · rcases d.livePatch_record_sources patchEq patchMember with inWorld | inResult
          · exact Or.inr (Or.inl inWorld)
          · exact Or.inr (Or.inr (Or.inr (Or.inl inResult)))
        · rcases paper_applicationRecords_sources scanMember with inFS | inPatch
          · have inWorld : (q, file) ∈ worldRecords d.selected :=
              List.mem_append_left _ (List.mem_append_left _ inFS)
            exact Or.inr (Or.inl inWorld)
          · rcases d.livePatch_record_sources patchEq inPatch with inWorld | inResult
            · exact Or.inr (Or.inl inWorld)
            · exact Or.inr (Or.inr (Or.inr (Or.inl inResult)))

/-- Prefix file occurrences agree without equating the whole-map collections. -/
theorem Prefix.paperRecords_occurrences (pre : Prefix m h executor prog start)
    (q : sig.Path) (file : File sig) :
    (q, file) ∈ recordOccurrences pre.paperRecords ↔ (q, file) ∈ pre.records := by
  simp only [Prefix.paperRecords, recordOccurrences_union, Set.mem_union,
    worldPaperRecords_occurrences, Prefix.records, List.mem_append, List.mem_flatMap]
  constructor
  · rintro (initial | ⟨record, ⟨d, atStep, inStep⟩, lookup⟩)
    · exact Or.inl initial
    · exact Or.inr ⟨d, atStep, (d.paperRecords_occurrences q file).mp ⟨record, inStep, lookup⟩⟩
  · rintro (initial | ⟨d, atStep, inStep⟩)
    · exact Or.inl initial
    · obtain ⟨record, inStep, lookup⟩ := (d.paperRecords_occurrences q file).mpr inStep
      exact Or.inr ⟨record, ⟨d, atStep, inStep⟩, lookup⟩

/-- Proof transport only: public consistency is still the map-level predicate. -/
theorem Prefix.paperRecords_consistent_iff (pre : Prefix m h executor prog start) :
    TimestampConsistent pre.paperRecords ↔ TimestampCompatible pre.records :=
  timestampConsistent_iff_normalized pre.paperRecords pre.records pre.paperRecords_occurrences

/-- The fixed-witness consistency bridge retains the whole-map public package. -/
theorem Prefix.paperRecords_witness_consistent_iff (pre : Prefix m h executor prog start)
    (witnesses : WitnessMap sig) :
    TimestampConsistent (pre.paperRecords ∪ witnessPaperRecords witnesses) ↔
      TimestampCompatible (pre.records ++ witnessRecords witnesses) := by
  apply timestampConsistent_iff_normalized
  intro q file
  rw [recordOccurrences_union, Set.mem_union, List.mem_append,
    pre.paperRecords_occurrences, witnessPaperRecords_occurrences]

/-- Every actual world contributes its whole current filesystem. -/
theorem world_fs_mem_paperRecords (world : World sig) : recordOfFS world.fs ∈ worldPaperRecords world := by
  exact Or.inl (Or.inl rfl)

/-- Every actual sandbox contributes its captured base, patch, and sandbox view. -/
theorem sandbox_mem_paperRecords {world : World sig} {slot : Nat} {sb : Sandbox sig}
    (present : FMap.get world.sandbox slot = some sb) :
    recordOfFS sb.base ∈ worldPaperRecords world ∧ sb.patch ∈ worldPaperRecords world ∧
      recordOfFS sb.view ∈ worldPaperRecords world := by
  refine ⟨Or.inr ⟨slot, sb, present, Or.inl rfl⟩, ?_, ?_⟩
  · exact Or.inr ⟨slot, sb, present, Or.inr (Or.inl rfl)⟩
  · exact Or.inr ⟨slot, sb, present, Or.inr (Or.inr rfl)⟩

/-- Each actual cache entry contributes its entire patch. -/
theorem cache_mem_worldPaperRecords {world : World sig} {key : Key sig} {memo : Memo sig}
    (present : FMap.get world.cache key = some memo) : memo.patch ∈ worldPaperRecords world := by
  exact Or.inl (Or.inr ⟨key, memo, present, rfl⟩)

/-- Every applied sandbox-mode patch yields the recorded successor filesystem. -/
theorem IncrDerivation.livePatch_after {before : World sig} {head : Head sig}
    {after : World sig} {returned : Option Chunk}
    (probe : IncrDerivation m before head after returned) {patch : Patch sig}
    (chosen : probe.livePatch = some patch) : after.fs = applyPatch before.fs patch := by
  cases probe <;> simp_all [IncrDerivation.livePatch, closeWorld, standaloneWorld]

/-- Vanilla applies its selected result patch to the current filesystem. -/
theorem VanillaDerivation.resultPatch_after {before : World sig} {head : Head sig}
    {after : World sig} {returned : Option Chunk}
    (probe : VanillaDerivation m before head after returned) :
    after.fs = applyPatch before.fs probe.result.patch := by
  cases probe <;> simp_all [VanillaDerivation.result, closeWorld, standaloneWorld]

/-- The actual live application result is the recorded probe successor. -/
theorem StepDerivation.livePatch_after (d : StepDerivation m h executor prog)
    {patch : Patch sig} (chosen : d.livePatch = some patch) :
    d.after.fs = applyPatch d.selected.fs patch := by
  cases executor with
  | incr => exact IncrDerivation.livePatch_after d.probe chosen
  | vanilla =>
    have same : (VanillaDerivation.result d.probe).patch = patch := Option.some.inj chosen
    rw [← same]
    exact VanillaDerivation.resultPatch_after d.probe

/-- Semantic application outputs are actual call or successor filesystems. -/
theorem StepDerivation.applicationPaperRecords_subset_actual (d : StepDerivation m h executor prog) :
    d.applicationPaperRecords ⊆ d.callPaperRecords ∪ worldPaperRecords d.after := by
  intro record member
  rcases member with ⟨fs, chosen, rfl⟩ | ⟨patch, chosen, rfl⟩
  · exact Or.inl ⟨fs, d.sandboxApplication_callFS chosen, rfl⟩
  · rw [← d.livePatch_after chosen]
    exact Or.inr (world_fs_mem_paperRecords d.after)

/-- Step and prefix collectors explicitly retain their complete maps. -/
theorem StepDerivation.beforePaperRecords_subset (d : StepDerivation m h executor prog) :
    worldPaperRecords d.before ⊆ d.paperRecords := by
  intro record member
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl member))))

theorem Prefix.initialPaperRecords_subset (pre : Prefix m h executor prog start) :
    worldPaperRecords start ⊆ pre.paperRecords := by
  intro record member
  exact Or.inl member

theorem Prefix.stepPaperRecords_subset (pre : Prefix m h executor prog start)
    {d : StepDerivation m h executor prog} (member : d ∈ pre.trace) :
    d.paperRecords ⊆ pre.paperRecords := by
  intro record recorded
  exact Or.inr ⟨d, member, recorded⟩

end
end Incr.Incr
