import Incr.IncrPP.Reuse.HitMatching

/-!
# Timestamp consistency for a fresh result patch

The timestamp condition is path-local: a finite patch has at most one
write record at each path. Fresh records need not have globally distinct
timestamps from each other.
-/

namespace Incr.IncrPP

noncomputable section

variable {sig : Signature}

/-- Every patch record is an actual write at the same path. -/
theorem patchRecord_lookup {patch : Patch sig} {q : sig.Path} {file : File sig}
    (member : (q, file) ∈ patchRecords patch) : FMap.get patch q = some (.write file) := by
  unfold patchRecords at member
  obtain ⟨entry, inEntries, mapped⟩ := List.mem_filterMap.mp member
  rcases entry with ⟨path, edit⟩
  cases edit with
  | delete => simp at mapped
  | write written =>
    simp only [Option.some.injEq, Prod.mk.injEq] at mapped
    obtain ⟨rfl, rfl⟩ := mapped
    exact Finmap.lookup_eq_some_iff.mpr (Multiset.mem_toList.mp inEntries)

/-- A single finite patch is timestamp-consistent because each path has one edit. -/
theorem patchRecords_consistent (patch : Patch sig) : TimestampCompatible (patchRecords patch) := by
  intro q first second firstAt secondAt sameTime
  have firstLookup := patchRecord_lookup firstAt
  have secondLookup := patchRecord_lookup secondAt
  rw [firstLookup] at secondLookup
  cases Option.some.inj secondLookup
  rfl

/-- Adding a patch fresh against all existing records preserves timestamp consistency. -/
theorem TimestampCompatible.add_fresh_patch {records : Records sig} {patch : Patch sig}
    (consistent : TimestampCompatible records)
    (fresh : ∀ q file, FMap.get patch q = some (.write file) →
      ∀ q' old, (q', old) ∈ records → file.mtime ≠ old.mtime) :
    TimestampCompatible (records ++ patchRecords patch) := by
  intro q first second firstAt secondAt sameTime
  rcases List.mem_append.mp firstAt with firstOld | firstNew <;>
    rcases List.mem_append.mp secondAt with secondOld | secondNew
  · exact consistent q first second firstOld secondOld sameTime
  · exact False.elim (fresh q second (patchRecord_lookup secondNew) q first firstOld sameTime.symm)
  · exact False.elim (fresh q first (patchRecord_lookup firstNew) q second secondOld sameTime)
  · exact patchRecords_consistent patch q first second firstNew secondNew sameTime

/-- Every actual patch write occurs in the patch's record collection. -/
theorem patchRecord_of_lookup {patch : Patch sig} {q : sig.Path} {file : File sig}
    (lookup : FMap.get patch q = some (.write file)) : (q, file) ∈ patchRecords patch := by
  exact List.mem_filterMap.mpr ⟨⟨q, .write file⟩,
    Multiset.mem_toList.mpr (Finmap.lookup_eq_some_iff.mp lookup), rfl⟩

/-- A file after applying a patch comes from the original filesystem or that patch. -/
theorem applyPatch_record_sources {fs : FS sig} {patch : Patch sig}
    {record : sig.Path × File sig} (member : record ∈ fsRecords (applyPatch fs patch)) :
    record ∈ fsRecords fs ++ patchRecords patch := by
  have lookup := get_of_mem_fsRecords member
  cases editAt : FMap.get patch record.1 with
  | none =>
    rw [applyPatch_get_none editAt] at lookup
    exact List.mem_append_left _ (mem_fsRecords_of_get lookup)
  | some edit =>
    cases edit with
    | delete =>
      rw [applyPatch_get_delete editAt] at lookup
      contradiction
    | write file =>
      rw [applyPatch_get_write editAt] at lookup
      cases Option.some.inj lookup
      exact List.mem_append_right _ (patchRecord_of_lookup editAt)

/-- Each scan lookup comes from the initial filesystem or an actually scanned write. -/
theorem scan_lookup_sources (entries : List (Sigma fun _ : sig.Path => Edit sig)) (fs : FS sig)
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
            by_cases same : q = key
            · subst key
              rw [FMap.get_set_self] at origin
              cases Option.some.inj origin
              exact Or.inr (List.mem_cons_self)
            · exact Or.inl (by simpa only [FMap.get_set_other same] using origin)
          | delete =>
            by_cases same : q = key
            · subst key
              simp only [FMap.get_erase_self] at origin
              contradiction
            · exact Or.inl (by simpa only [FMap.get_erase_of_ne same] using origin)
      · exact Or.inr (List.mem_cons_of_mem _ inserted)

/-- Intermediate patch applications add only original filesystem or patch records. -/
theorem applicationRecords_sources {fs : FS sig} {patch : Patch sig}
    {record : sig.Path × File sig} (member : record ∈ applicationRecords fs patch) :
    record ∈ fsRecords fs ++ patchRecords patch := by
  obtain ⟨snapshot, scanned, found⟩ := List.mem_flatMap.mp member
  rcases scan_lookup_sources patch.entries.toList fs scanned (get_of_mem_fsRecords found) with old | write
  · exact List.mem_append_left _ (mem_fsRecords_of_get old)
  · exact List.mem_append_right _ (List.mem_filterMap.mpr ⟨⟨record.1, .write record.2⟩, write, rfl⟩)

/-- An actual sandbox lookup retains its base and patch records in the world collection. -/
theorem world_sandbox_record {world : World sig} {slot : Nat} {sb : Sandbox sig}
    (lookup : FMap.get world.sandbox slot = some sb) {record : sig.Path × File sig}
    (member : record ∈ fsRecords sb.base ∨ record ∈ patchRecords sb.patch) : record ∈ worldRecords world := by
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨⟨slot, sb⟩, Multiset.mem_toList.mpr (Finmap.lookup_eq_some_iff.mp lookup), ?_⟩
  exact List.mem_append.mpr member

variable {m : CommandModel sig}

/-- Every vanilla probe leaves the cache unchanged. -/
theorem VanillaDerivation.cache_unchanged {before after : World sig} {head : Head sig}
    {out : Option Chunk} (d : VanillaDerivation m before head after out) : after.cache = before.cache := by
  cases d <;> rfl

/-- A vanilla successor's world records come from its selected world or actual call patch. -/
theorem VanillaDerivation.after_record_sources {before after : World sig} {head : Head sig}
    {out : Option Chunk} (d : VanillaDerivation m before head after out)
    {record : sig.Path × File sig} (member : record ∈ worldRecords after) :
    record ∈ worldRecords before ++ patchRecords (VanillaDerivation.result d).patch := by
  have fsEffect := d.executing_effects.2
  have cacheEq := d.cache_unchanged
  simp only [worldRecords, List.mem_append] at member
  rcases member with (fs | cache) | sandbox
  · rw [fsEffect] at fs
    rcases List.mem_append.mp (applyPatch_record_sources fs) with old | fresh
    · apply List.mem_append_left
      simp only [worldRecords, List.mem_append]
      exact Or.inl (Or.inl old)
    · exact List.mem_append_right _ fresh
  · apply List.mem_append_left
    simp only [worldRecords, List.mem_append]
    exact Or.inl (Or.inr (cacheEq ▸ cache))
  · obtain ⟨⟨slot, sb⟩, entry, inside⟩ := List.mem_flatMap.mp sandbox
    have lookup : FMap.get after.sandbox slot = some sb :=
      Finmap.lookup_eq_some_iff.mpr (Multiset.mem_toList.mp entry)
    obtain ⟨old, oldLookup, _, same⟩ := ProbeDerivation.sandbox_ancestor (executor := .vanilla) d lookup
    have equal : sb = old := same rfl
    subst sb
    exact List.mem_append_left _ (world_sandbox_record oldLookup (List.mem_append.mp inside))

/-- Vanilla recorded call and applied patches are the actual selected filesystem and result patch. -/
theorem VanillaDerivation.record_views {before after : World sig} {head : Head sig}
    {out : Option Chunk} (d : VanillaDerivation m before head after out) :
    VanillaDerivation.callFS d = some before.fs ∧ VanillaDerivation.appliedPatch d = (VanillaDerivation.result d).patch := by
  cases d <;> exact ⟨rfl, rfl⟩

variable {h : Host sig} {prog : sig.Prog} {start : World sig}

/-- An actual vanilla step records only the prior prefix or its newly executed result patch. -/
theorem StepDerivation.vanilla_record_sources (host : HostWellFormed m h)
    (pre : Prefix m h .vanilla prog start) (operational : Operational pre)
    (d : StepDerivation m h .vanilla prog) (before : d.before = pre.final) :
    ∀ record ∈ d.records, record ∈ pre.records ++ patchRecords (VanillaDerivation.result d.probe).patch := by
  have allowed : h.select prog pre.final d.selection d.selected := by simpa [before] using d.host
  have selected := selected_world_records host pre operational d.selection d.selected allowed
  have views := d.probe.record_views
  intro record member
  simp only [StepDerivation.records, ProbeDerivation.callFS, ProbeDerivation.result,
    ProbeDerivation.appliedPatch, views.1, views.2, List.mem_append] at member
  rcases member with (((((old | chosen) | after) | patch) | callFS) | applied) | scanned
  · apply List.mem_append_left
    apply pre.final_world_records
    simpa only [before] using old
  · exact List.mem_append_left _ (selected record chosen)
  · rcases List.mem_append.mp (d.probe.after_record_sources after) with old | fresh
    · exact List.mem_append_left _ (selected record old)
    · exact List.mem_append_right _ fresh
  · exact List.mem_append_right _ patch
  · apply List.mem_append_left
    apply selected record
    simp only [worldRecords, List.mem_append]
    exact Or.inl (Or.inl callFS)
  · exact List.mem_append_right _ applied
  · rcases List.mem_append.mp (applicationRecords_sources scanned) with old | fresh
    · apply List.mem_append_left
      apply selected record
      simp only [worldRecords, List.mem_append]
      exact Or.inl (Or.inl old)
    · exact List.mem_append_right _ fresh

/-- A fresh vanilla target extension preserves operational and fixed-witness timestamp consistency. -/
theorem Operational.vanilla_snoc_fresh (host : HostWellFormed m h)
    (pre post : Prefix m h .vanilla prog start) (operational : Operational pre)
    (witnesses : WitnessMap sig) (consistent : TimestampCompatible (pre.records ++ witnessRecords witnesses))
    (d : StepDerivation m h .vanilla prog) (before : d.before = pre.final)
    (joined : post.trace = pre.trace ++ [d])
    (freshLocal : FreshPatch (VanillaDerivation.result d.probe).patch d.selected.fs d.selected.fs)
    (freshRecords : ∀ q file, FMap.get (VanillaDerivation.result d.probe).patch q = some (.write file) →
      ∀ q' old, (q', old) ∈ pre.records ++ witnessRecords witnesses → file.mtime ≠ old.mtime) :
    Operational post ∧ TimestampCompatible (post.records ++ witnessRecords witnesses) := by
  have bigConsistent := TimestampCompatible.add_fresh_patch consistent freshRecords
  have stepSources := d.vanilla_record_sources host pre operational before
  have postConsistent : TimestampCompatible (post.records ++ witnessRecords witnesses) := by
    apply TimestampCompatible.mono ?_ bigConsistent
    intro record member
    simp only [Prefix.records, joined, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.mem_append, List.not_mem_nil, or_false] at member ⊢
    rcases member with (initial | oldStep | currentStep) | fixed
    · exact Or.inl (Or.inl (Or.inl initial))
    · exact Or.inl (Or.inl (Or.inr oldStep))
    · rcases List.mem_append.mp (stepSources record currentStep) with old | fresh
      · simp only [Prefix.records, List.mem_append] at old
        rcases old with initial | prior
        · exact Or.inl (Or.inl (Or.inl initial))
        · exact Or.inl (Or.inl (Or.inr prior))
      · exact Or.inr fresh
    · exact Or.inl (Or.inr fixed)
  constructor
  · constructor
    · intro step member
      rw [joined] at member
      rcases List.mem_append.mp member with old | new
      · exact operational.timestamps step old
      · simp only [List.mem_singleton] at new
        subst step
        simp only [ProbeDerivation.TimestampCondition, ProbeDerivation.callFS,
          ProbeDerivation.result, d.probe.record_views.1]
        exact freshLocal
    · intro n bound
      apply (tracePaperRecords_consistent_iff start (post.trace.take n)).mpr
      apply TimestampCompatible.mono ?_ postConsistent
      intro record member
      simp only [List.mem_append, List.mem_flatMap] at member
      rcases member with initial | ⟨step, stepAt, found⟩
      · simp only [Prefix.records, List.mem_append]
        exact Or.inl (Or.inl initial)
      · simp only [Prefix.records, List.mem_append, List.mem_flatMap]
        exact Or.inl (Or.inr ⟨step, List.take_subset n post.trace stepAt, found⟩)
  · exact postConsistent

/-- A merged patch contains only records from its earlier or later patch. -/
theorem merge_patch_record_sources {left right : Patch sig} {record : sig.Path × File sig}
    (member : record ∈ patchRecords (left ⊎ right)) : record ∈ patchRecords left ++ patchRecords right := by
  have lookup := patchRecord_lookup member
  rw [FMap.get_merge_elim] at lookup
  cases rightAt : FMap.get right record.1 with
  | none =>
    have leftAt : FMap.get left record.1 = some (.write record.2) := by simpa [rightAt] using lookup
    exact List.mem_append_left _ (patchRecord_of_lookup leftAt)
  | some edit =>
    have equal : edit = .write record.2 := by simpa [rightAt] using lookup
    rw [equal] at rightAt
    exact List.mem_append_right _ (patchRecord_of_lookup rightAt)

/-- A retained cache entry contributes its patch records to the cache record collection. -/
theorem cache_patch_record {cache : Cache sig} {key : Key sig} {memo : Memo sig}
    (lookup : FMap.get cache key = some memo) {record : sig.Path × File sig}
    (member : record ∈ patchRecords memo.patch) : record ∈ cacheRecords cache := by
  exact List.mem_flatMap.mpr ⟨⟨key, memo⟩,
    Multiset.mem_toList.mpr (Finmap.lookup_eq_some_iff.mp lookup), member⟩

/-- Store, retain, and erase policies add at most the candidate memo's patch records. -/
theorem CacheUpdate.record_sources {cache next : Cache sig} {key : Key sig} {memo : Memo sig}
    (update : CacheUpdate cache key memo next) {record : sig.Path × File sig}
    (member : record ∈ cacheRecords next) : record ∈ cacheRecords cache ++ patchRecords memo.patch := by
  rcases update with store | keep | erase
  · subst next
    obtain ⟨⟨otherKey, otherMemo⟩, entry, inside⟩ := List.mem_flatMap.mp member
    have lookup : FMap.get (FMap.set cache key memo) otherKey = some otherMemo :=
      Finmap.lookup_eq_some_iff.mpr (Multiset.mem_toList.mp entry)
    by_cases same : otherKey = key
    · subst otherKey
      rw [FMap.get_set_self] at lookup
      cases Option.some.inj lookup
      exact List.mem_append_right _ inside
    · rw [FMap.get_set_other same] at lookup
      exact List.mem_append_left _ (cache_patch_record lookup inside)
  · subst next
    exact List.mem_append_left _ member
  · subst next
    obtain ⟨⟨otherKey, otherMemo⟩, entry, inside⟩ := List.mem_flatMap.mp member
    have lookup : FMap.get (cache ∖ key) otherKey = some otherMemo :=
      Finmap.lookup_eq_some_iff.mpr (Multiset.mem_toList.mp entry)
    have different : otherKey ≠ key := lookup_erase_ne lookup
    rw [FMap.get_erase_of_ne different] at lookup
    exact List.mem_append_left _ (cache_patch_record lookup inside)

/-- An executing live step's cache records come from the selected world or its new result patch. -/
theorem LiveDerivation.executing_cache_records {before after : World sig} {head : Head sig}
    {out : Option Chunk} (d : LiveDerivation m before head after out)
    (executing : LiveDerivation.callFS d = some before.fs) :
    ∀ record ∈ cacheRecords after.cache,
      record ∈ worldRecords before ++ patchRecords (LiveDerivation.result d).patch := by
  cases d
  all_goals simp only [LiveDerivation.callFS] at executing
  all_goals try contradiction
  all_goals simp only [LiveDerivation.result, closeWorld, standaloneWorld]
  case cacheCloseMiss =>
    rename_i p i sb s r es buffers cache hcacheable hbuffer hsandbox hinput houtput hcall hstatus hflag hcache hput
    intro record member
    rcases List.mem_append.mp (CacheUpdate.record_sources hcache member) with old | new
    · apply List.mem_append_left
      simp only [worldRecords, List.mem_append]
      exact Or.inl (Or.inr old)
    · change record ∈ patchRecords (sb.patch ⊎ r.patch) at new
      rcases List.mem_append.mp (merge_patch_record_sources new) with old | fresh
      · exact List.mem_append_left _ (world_sandbox_record hsandbox (Or.inr old))
      · exact List.mem_append_right _ fresh
  case cacheStandaloneMiss =>
    rename_i p s r es cache hcacheable hstdin hcall hstatus hflag hcache
    intro record member
    rcases List.mem_append.mp (CacheUpdate.record_sources hcache member) with old | fresh
    · apply List.mem_append_left
      simp only [worldRecords, List.mem_append]
      exact Or.inl (Or.inr old)
    · exact List.mem_append_right _ fresh
  all_goals
    intro record member
    apply List.mem_append_left
    simp only [worldRecords, List.mem_append]
    exact Or.inl (Or.inr member)

/-- An executing live successor retains only selected-world or new call-patch records. -/
theorem LiveDerivation.executing_after_records {before after : World sig} {head : Head sig}
    {out : Option Chunk} (d : LiveDerivation m before head after out)
    (executing : LiveDerivation.callFS d = some before.fs)
    {record : sig.Path × File sig} (member : record ∈ worldRecords after) :
    record ∈ worldRecords before ++ patchRecords (LiveDerivation.result d).patch := by
  have fsEffect := (d.executing_effects executing).2
  simp only [worldRecords, List.mem_append] at member
  rcases member with (fs | cache) | sandbox
  · rw [fsEffect] at fs
    rcases List.mem_append.mp (applyPatch_record_sources fs) with old | fresh
    · apply List.mem_append_left
      simp only [worldRecords, List.mem_append]
      exact Or.inl (Or.inl old)
    · exact List.mem_append_right _ fresh
  · exact d.executing_cache_records executing record cache
  · obtain ⟨⟨slot, sb⟩, entry, inside⟩ := List.mem_flatMap.mp sandbox
    have lookup : FMap.get after.sandbox slot = some sb :=
      Finmap.lookup_eq_some_iff.mpr (Multiset.mem_toList.mp entry)
    rcases d.history_effect lookup with own | foreign
    · obtain ⟨p, head, openInput, old, hin, hout, prior, rfl⟩ := own
      rcases List.mem_append.mp inside with base | patch
      · exact List.mem_append_left _ (world_sandbox_record prior (Or.inl base))
      · change record ∈ patchRecords (old.patch ⊎ (LiveDerivation.result d).patch) at patch
        rcases List.mem_append.mp (merge_patch_record_sources patch) with oldPatch | fresh
        · exact List.mem_append_left _ (world_sandbox_record prior (Or.inr oldPatch))
        · exact List.mem_append_right _ fresh
    · obtain ⟨prior, _⟩ := foreign
      exact List.mem_append_left _ (world_sandbox_record prior (List.mem_append.mp inside))

/-- Executing live rules apply their own retained call patch. -/
theorem LiveDerivation.executing_applied {before after : World sig} {head : Head sig}
    {out : Option Chunk} (d : LiveDerivation m before head after out)
    (executing : LiveDerivation.callFS d = some before.fs) :
    LiveDerivation.appliedPatch d = (LiveDerivation.result d).patch := by
  cases d <;> simp_all [LiveDerivation.callFS, LiveDerivation.appliedPatch, LiveDerivation.result]

/-- An executing live step records only the prior prefix or its newly executed result patch. -/
theorem StepDerivation.live_executing_record_sources (host : HostWellFormed m h)
    (pre : Prefix m h .live prog start) (operational : Operational pre)
    (d : StepDerivation m h .live prog) (before : d.before = pre.final)
    (executing : LiveDerivation.callFS d.probe = some d.selected.fs) :
    ∀ record ∈ d.records, record ∈ pre.records ++ patchRecords (LiveDerivation.result d.probe).patch := by
  have allowed : h.select prog pre.final d.selection d.selected := by simpa [before] using d.host
  have selected := selected_world_records host pre operational d.selection d.selected allowed
  have appliedEq := d.probe.executing_applied executing
  intro record member
  simp only [StepDerivation.records, ProbeDerivation.callFS, ProbeDerivation.result,
    ProbeDerivation.appliedPatch, executing, appliedEq, List.mem_append] at member
  rcases member with (((((old | chosen) | after) | patch) | callFS) | applied) | scanned
  · apply List.mem_append_left
    apply pre.final_world_records
    simpa only [before] using old
  · exact List.mem_append_left _ (selected record chosen)
  · rcases List.mem_append.mp (d.probe.executing_after_records executing after) with old | fresh
    · exact List.mem_append_left _ (selected record old)
    · exact List.mem_append_right _ fresh
  · exact List.mem_append_right _ patch
  · apply List.mem_append_left
    apply selected record
    simp only [worldRecords, List.mem_append]
    exact Or.inl (Or.inl callFS)
  · exact List.mem_append_right _ applied
  · rcases List.mem_append.mp (applicationRecords_sources scanned) with old | fresh
    · apply List.mem_append_left
      apply selected record
      simp only [worldRecords, List.mem_append]
      exact Or.inl (Or.inl old)
    · exact List.mem_append_right _ fresh

/-- A fresh executing live target extension preserves operational and fixed-witness consistency. -/
theorem Operational.live_snoc_fresh (host : HostWellFormed m h)
    (pre post : Prefix m h .live prog start) (operational : Operational pre)
    (witnesses : WitnessMap sig) (consistent : TimestampCompatible (pre.records ++ witnessRecords witnesses))
    (d : StepDerivation m h .live prog) (before : d.before = pre.final)
    (joined : post.trace = pre.trace ++ [d])
    (executing : LiveDerivation.callFS d.probe = some d.selected.fs)
    (freshLocal : FreshPatch (LiveDerivation.result d.probe).patch d.selected.fs d.selected.fs)
    (freshRecords : ∀ q file, FMap.get (LiveDerivation.result d.probe).patch q = some (.write file) →
      ∀ q' old, (q', old) ∈ pre.records ++ witnessRecords witnesses → file.mtime ≠ old.mtime) :
    Operational post ∧ TimestampCompatible (post.records ++ witnessRecords witnesses) := by
  have bigConsistent := TimestampCompatible.add_fresh_patch consistent freshRecords
  have stepSources := d.live_executing_record_sources host pre operational before executing
  have postConsistent : TimestampCompatible (post.records ++ witnessRecords witnesses) := by
    apply TimestampCompatible.mono ?_ bigConsistent
    intro record member
    simp only [Prefix.records, joined, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.mem_append, List.not_mem_nil, or_false] at member ⊢
    rcases member with (initial | oldStep | currentStep) | fixed
    · exact Or.inl (Or.inl (Or.inl initial))
    · exact Or.inl (Or.inl (Or.inr oldStep))
    · rcases List.mem_append.mp (stepSources record currentStep) with old | fresh
      · simp only [Prefix.records, List.mem_append] at old
        rcases old with initial | prior
        · exact Or.inl (Or.inl (Or.inl initial))
        · exact Or.inl (Or.inl (Or.inr prior))
      · exact Or.inr fresh
    · exact Or.inl (Or.inr fixed)
  constructor
  · constructor
    · intro step member
      rw [joined] at member
      rcases List.mem_append.mp member with old | new
      · exact operational.timestamps step old
      · simp only [List.mem_singleton] at new
        subst step
        simp only [ProbeDerivation.TimestampCondition, ProbeDerivation.callFS,
          ProbeDerivation.result, executing]
        exact freshLocal
    · intro n bound
      apply (tracePaperRecords_consistent_iff start (post.trace.take n)).mpr
      apply TimestampCompatible.mono ?_ postConsistent
      intro record member
      simp only [List.mem_append, List.mem_flatMap] at member
      rcases member with initial | ⟨step, stepAt, found⟩
      · simp only [Prefix.records, List.mem_append]
        exact Or.inl (Or.inl initial)
      · simp only [Prefix.records, List.mem_append, List.mem_flatMap]
        exact Or.inl (Or.inr ⟨step, List.take_subset n post.trace stepAt, found⟩)
  · exact postConsistent

end
end IncrPP
end Incr
