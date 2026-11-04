import Incr.Incr.Bisimulation.StepMatching

/-! # Record origins for constructed `thm:paper-bisimulation` successors

Record origins use the actual filesystem and patch collectors. These lemmas
preserve timestamp compatibility without identifying whole-map witnesses.
-/

namespace Incr.Incr.RecordInventory

noncomputable section

variable {sig : Signature} {m : CommandModel sig} {h : Host sig}
  {executor : Executor} {prog : sig.Prog} {start : World sig}

/-- Each primitive world map takes its file records from the given inventory. -/
structure WorldOrigins (records : Records sig) (w : World sig) : Prop where
  fs : ∀ record ∈ fsRecords w.fs, record ∈ records
  cache : ∀ record ∈ cacheRecords w.cache, record ∈ records
  base : ∀ i sb, FMap.get w.sandbox i = some sb →
    ∀ record ∈ fsRecords sb.base, record ∈ records
  patch : ∀ i sb, FMap.get w.sandbox i = some sb →
    ∀ record ∈ patchRecords sb.patch, record ∈ records

theorem WorldOrigins.mono {records records' : Records sig} {w : World sig}
    (origins : WorldOrigins records w) (sub : ∀ record ∈ records, record ∈ records') :
    WorldOrigins records' w := by
  exact ⟨fun r hr => sub r (origins.fs r hr),
    fun r hr => sub r (origins.cache r hr),
    fun i sb get r hr => sub r (origins.base i sb get r hr),
    fun i sb get r hr => sub r (origins.patch i sb get r hr)⟩

theorem WorldOrigins.records {records : Records sig} {w : World sig}
    (origins : WorldOrigins records w) : ∀ record ∈ worldRecords w, record ∈ records := by
  intro record member
  simp only [worldRecords, List.mem_append, List.mem_flatMap] at member
  rcases member with (fs | cache) | ⟨⟨i, sb⟩, entry, inside⟩
  · exact origins.fs record fs
  · exact origins.cache record cache
  · have get : FMap.get w.sandbox i = some sb :=
      Finmap.lookup_eq_some_iff.mpr (Multiset.mem_toList.mp entry)
    rcases inside with (base | patch) | scan
    · exact origins.base i sb get record base
    · exact origins.patch i sb get record patch
    · rcases List.mem_append.mp (PrefixProperties.application_records_sources scan) with base | patch
      · exact origins.base i sb get record base
      · exact origins.patch i sb get record patch

theorem WorldOrigins.of_records {records : Records sig} {w : World sig}
    (origins : ∀ record ∈ worldRecords w, record ∈ records) : WorldOrigins records w := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro record member
    exact origins record (List.mem_append_left _ (List.mem_append_left _ member))
  · intro record member
    exact origins record (List.mem_append_left _ (List.mem_append_right _ member))
  · intro i sb get record member
    apply origins record
    apply List.mem_append_right
    apply List.mem_flatMap.mpr
    refine ⟨⟨i, sb⟩, Multiset.mem_toList.mpr (Finmap.lookup_eq_some_iff.mp get), ?_⟩
    exact List.mem_append_left _ (List.mem_append_left _ member)
  · intro i sb get record member
    apply origins record
    apply List.mem_append_right
    apply List.mem_flatMap.mpr
    refine ⟨⟨i, sb⟩, Multiset.mem_toList.mpr (Finmap.lookup_eq_some_iff.mp get), ?_⟩
    exact List.mem_append_left _ (List.mem_append_right _ member)

theorem patch_record_of_get {patch : Patch sig} {q : sig.Path} {file : File sig}
    (get : FMap.get patch q = some (.write file)) : (q, file) ∈ patchRecords patch := by
  exact List.mem_filterMap.mpr ⟨⟨q, .write file⟩,
    Multiset.mem_toList.mpr (Finmap.lookup_eq_some_iff.mp get), rfl⟩

theorem merge_patch_sources {left right : Patch sig} {record : sig.Path × File sig}
    (member : record ∈ patchRecords (left ⊎ right)) :
    record ∈ patchRecords left ++ patchRecords right := by
  have get := C8Steps.patch_record_get member
  rw [FMap.get_merge_elim] at get
  cases rightGet : FMap.get right record.1 with
  | none =>
    have leftGet : FMap.get left record.1 = some (.write record.2) := by
      simpa [rightGet] using get
    exact List.mem_append_left _ (patch_record_of_get leftGet)
  | some edit =>
    have same : edit = .write record.2 := by simpa [rightGet] using get
    rw [same] at rightGet
    exact List.mem_append_right _ (patch_record_of_get rightGet)

theorem cache_patch_sources {cache : Cache sig} {key : Key sig} {memo : Memo sig}
    (get : FMap.get cache key = some memo) {record : sig.Path × File sig}
    (member : record ∈ patchRecords memo.patch) : record ∈ cacheRecords cache := by
  exact List.mem_flatMap.mpr ⟨⟨key, memo⟩,
    Multiset.mem_toList.mpr (Finmap.lookup_eq_some_iff.mp get), member⟩

theorem cache_set_sources {cache : Cache sig} {key : Key sig} {memo : Memo sig}
    {record : sig.Path × File sig} (member : record ∈ cacheRecords (FMap.set cache key memo)) :
    record ∈ cacheRecords cache ++ patchRecords memo.patch := by
  classical
  obtain ⟨⟨key', memo'⟩, entry, inside⟩ := List.mem_flatMap.mp member
  have get : FMap.get (FMap.set cache key memo) key' = some memo' :=
    Finmap.lookup_eq_some_iff.mpr (Multiset.mem_toList.mp entry)
  by_cases same : key' = key
  · subst key'
    rw [FMap.get_set_self] at get
    cases Option.some.inj get
    exact List.mem_append_right _ inside
  · rw [FMap.get_set_other same] at get
    exact List.mem_append_left _ (cache_patch_sources get inside)

/-- Host selection does not introduce filesystem or patch records. -/
theorem selection_origins {trace : Trace m h executor prog}
    {before selected : World sig} {selection : Selection sig} {records : Records sig}
    (origins : WorldOrigins records before)
    (discipline : SelectionDiscipline trace before selection selected) :
    WorldOrigins records selected := by
  obtain ⟨fs, _, cache, init, _⟩ := discipline
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [fs] using origins.fs
  · simpa only [cache] using origins.cache
  · intro i sb get record member
    cases selectionInit : selection.init with
    | none =>
      simp only [selectionInit] at init
      rw [init.1] at get
      exact origins.base i sb get record member
    | some initialization =>
      simp only [selectionInit] at init
      rw [init.2.2.2.2] at get
      have initial := initialSandboxes_get_eq initialization before.fs get
      rw [initial] at member
      exact origins.fs record member
  · intro i sb get record member
    cases selectionInit : selection.init with
    | none =>
      simp only [selectionInit] at init
      rw [init.1] at get
      exact origins.patch i sb get record member
    | some initialization =>
      simp only [selectionInit] at init
      rw [init.2.2.2.2] at get
      have initial := initialSandboxes_get_eq initialization before.fs get
      have get := C8Steps.patch_record_get member
      simp [initial, Sandbox.initial, FMap.get] at get

/-- Selected worlds retain only records already present in their prefix. -/
theorem selected_records (host : HostWellFormed m h)
    (pre : Prefix m h executor prog start) (operational : Operational pre)
    {selection : Selection sig} {selected : World sig}
    (chosen : h.select prog pre.final selection selected) :
    ∀ record ∈ worldRecords selected, record ∈ pre.records := by
  apply WorldOrigins.records
  exact selection_origins
    (WorldOrigins.of_records (C8Steps.final_world_records pre))
    (host.selectionDiscipline _ _ _ pre operational _ _ chosen)

/-- Fields unrelated to retained files do not affect record origins. -/
theorem WorldOrigins.congr {records : Records sig} {w w' : World sig}
    (origins : WorldOrigins records w) (fs : w'.fs = w.fs)
    (cache : w'.cache = w.cache) (sandboxes : w'.sandbox = w.sandbox) :
    WorldOrigins records w' := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [fs] using origins.fs
  · simpa only [cache] using origins.cache
  · simpa only [sandboxes] using origins.base
  · simpa only [sandboxes] using origins.patch

theorem WorldOrigins.apply_patch {records : Records sig} {w : World sig}
    (origins : WorldOrigins records w) (patch : Patch sig)
    (new : ∀ record ∈ patchRecords patch, record ∈ records) :
    WorldOrigins records {w with fs := applyPatch w.fs patch} := by
  refine ⟨?_, origins.cache, origins.base, origins.patch⟩
  intro record member
  rcases List.mem_append.mp (PrefixProperties.view_record_sources member) with old | fresh
  · exact origins.fs record old
  · exact new record fresh

theorem WorldOrigins.set_cache {records : Records sig} {w : World sig}
    (origins : WorldOrigins records w) (key : Key sig) (memo : Memo sig)
    (new : ∀ record ∈ patchRecords memo.patch, record ∈ records) :
    WorldOrigins records {w with cache := FMap.set w.cache key memo} := by
  refine ⟨origins.fs, ?_, origins.base, origins.patch⟩
  intro record member
  rcases List.mem_append.mp (cache_set_sources member) with old | fresh
  · exact origins.cache record old
  · exact new record fresh

theorem WorldOrigins.erase_sandbox {records : Records sig} {w : World sig}
    (origins : WorldOrigins records w) (i : Nat) :
    WorldOrigins records {w with sandbox := w.sandbox ∖ i} := by
  have previous {j : Nat} {sb : Sandbox sig}
      (get : FMap.get (w.sandbox ∖ i) j = some sb) : FMap.get w.sandbox j = some sb := by
    by_cases same : j = i
    · subst j; simp [FMap.get_erase_self] at get
    · rwa [FMap.get_erase_of_ne same] at get
  exact ⟨origins.fs, origins.cache,
    fun j sb get => origins.base j sb (previous get),
    fun j sb get => origins.patch j sb (previous get)⟩

theorem WorldOrigins.set_sandbox {records : Records sig} {w : World sig}
    (origins : WorldOrigins records w) (i : Nat) (sb : Sandbox sig)
    (base : ∀ record ∈ fsRecords sb.base, record ∈ records)
    (patch : ∀ record ∈ patchRecords sb.patch, record ∈ records) :
    WorldOrigins records {w with sandbox := w.sandbox[i ↦ sb]} := by
  have previous {j : Nat} {other : Sandbox sig} (different : j ≠ i)
      (get : FMap.get (w.sandbox[i ↦ sb]) j = some other) :
      FMap.get w.sandbox j = some other := by rwa [FMap.get_set_other different] at get
  refine ⟨origins.fs, origins.cache, ?_, ?_⟩
  · intro j other get
    by_cases same : j = i
    · subst j
      rw [FMap.get_set_self] at get
      cases Option.some.inj get
      exact base
    · exact origins.base j other (previous same get)
  · intro j other get
    by_cases same : j = i
    · subst j
      rw [FMap.get_set_self] at get
      cases Option.some.inj get
      exact patch
    · exact origins.patch j other (previous same get)

theorem merge_origins {records : Records sig} {left right : Patch sig}
    (old : ∀ record ∈ patchRecords left, record ∈ records)
    (new : ∀ record ∈ patchRecords right, record ∈ records) :
    ∀ record ∈ patchRecords (left ⊎ right), record ∈ records := by
  intro record member
  exact (List.mem_append.mp (merge_patch_sources member)).elim (old record) (new record)

theorem sandbox_view_origins {records : Records sig} {w : World sig}
    (origins : WorldOrigins records w) {i : Nat} {sb : Sandbox sig}
    (get : FMap.get w.sandbox i = some sb) :
    ∀ record ∈ fsRecords sb.view, record ∈ records := by
  intro record member
  exact (List.mem_append.mp (PrefixProperties.view_record_sources member)).elim
    (origins.base i sb get record) (origins.patch i sb get record)

/-- All seven raw successors use only old records and their result patch. -/
theorem incr_after_origins {records : Records sig} {w after : World sig}
    {head : Head sig} {out : Option Chunk} (d : IncrDerivation m w head after out)
    (origins : WorldOrigins records w)
    (result : ∀ record ∈ patchRecords (IncrDerivation.result d).patch, record ∈ records) :
    WorldOrigins records after := by
  cases d with
  | pipelineOpen p i sb taken remaining r buffers out hb hs hi ho hc hstatus hflag hp =>
    exact (origins.set_sandbox i (sb.accumulate _ r hi ho)
      (origins.base i sb hs) (merge_origins (origins.patch i sb hs) result)).congr
      (applyPatch_empty w.fs) rfl rfl
  | uncacheClose p i sb s r es buffers out hn hb hs hc hstatus hflag hp =>
    exact ((origins.apply_patch _ (merge_origins (origins.patch i sb hs) result)).erase_sandbox i).congr rfl rfl rfl
  | cacheCloseMiss p i sb s r es buffers out cacheable hb hs hi ho miss hc hstatus hflag hp =>
    have combined := merge_origins (origins.patch i sb hs) result
    exact (((origins.apply_patch _ combined).erase_sandbox i).set_cache _
      (accumulatedMemo sb _ r es hi ho hflag) combined).congr rfl rfl rfl
  | cacheCloseHit p i sb s tail memo buffers out cacheable hb hs hi ho hm valid guard hp =>
    exact ((origins.apply_patch _ result).erase_sandbox i).congr rfl rfl rfl
  | uncacheStandalone p s r es cacheable hb hc hstatus =>
    exact (origins.apply_patch _ result).congr rfl rfl rfl
  | cacheStandaloneMiss p s r es cacheable hb miss hc hstatus hflag =>
    exact ((origins.apply_patch _ result).set_cache _
      ⟨es, r.patch, r.reads, r.writes, r.output, hflag⟩ result).congr rfl rfl rfl
  | cacheStandaloneHit p s memo cacheable hb hm valid flag =>
    exact (origins.apply_patch _ result).congr rfl rfl rfl

/-- A call filesystem is the selected live map or an existing sandbox view. -/
theorem incr_call_origins {records : Records sig} {w after : World sig}
    {head : Head sig} {out : Option Chunk} (d : IncrDerivation m w head after out)
    (origins : WorldOrigins records w) :
    ∀ fs, IncrDerivation.callFS d = some fs → ∀ record ∈ fsRecords fs, record ∈ records := by
  cases d with
  | pipelineOpen p i sb taken remaining r buffers out hb hs hi ho hc hstatus hflag hp =>
    intro fs same
    cases Option.some.inj same
    exact sandbox_view_origins origins hs
  | uncacheClose p i sb s r es buffers out hn hb hs hc hstatus hflag hp =>
    intro fs same
    cases Option.some.inj same
    exact sandbox_view_origins origins hs
  | cacheCloseMiss p i sb s r es buffers out cacheable hb hs hi ho miss hc hstatus hflag hp =>
    intro fs same
    cases Option.some.inj same
    exact sandbox_view_origins origins hs
  | cacheCloseHit => simp [IncrDerivation.callFS]
  | uncacheStandalone =>
    intro fs same
    cases Option.some.inj same
    exact origins.fs
  | cacheStandaloneMiss =>
    intro fs same
    cases Option.some.inj same
    exact origins.fs
  | cacheStandaloneHit => simp [IncrDerivation.callFS]

/-- Applied live patches include an old staged prefix only at a close. -/
theorem incr_live_origins {records : Records sig} {w after : World sig}
    {head : Head sig} {out : Option Chunk} (d : IncrDerivation m w head after out)
    (origins : WorldOrigins records w)
    (result : ∀ record ∈ patchRecords (IncrDerivation.result d).patch, record ∈ records) :
    ∀ patch, IncrDerivation.livePatch d = some patch →
      ∀ record ∈ patchRecords patch, record ∈ records := by
  cases d with
  | pipelineOpen => simp [IncrDerivation.livePatch]
  | uncacheClose p i sb s r es buffers out hn hb hs hc hstatus hflag hp =>
    intro patch same
    cases Option.some.inj same
    exact merge_origins (origins.patch i sb hs) result
  | cacheCloseMiss p i sb s r es buffers out cacheable hb hs hi ho miss hc hstatus hflag hp =>
    intro patch same
    cases Option.some.inj same
    exact merge_origins (origins.patch i sb hs) result
  | cacheCloseHit | uncacheStandalone | cacheStandaloneMiss | cacheStandaloneHit =>
    intro patch same
    cases Option.some.inj same
    exact result

/-- The three vanilla successors have the same primitive record-origin bound. -/
theorem vanilla_after_origins {records : Records sig} {w after : World sig}
    {head : Head sig} {out : Option Chunk} (d : VanillaDerivation m w head after out)
    (origins : WorldOrigins records w)
    (result : ∀ record ∈ patchRecords (VanillaDerivation.result d).patch, record ∈ records) :
    WorldOrigins records after := by
  cases d with
  | openStep => exact (origins.apply_patch _ result).congr rfl rfl rfl
  | closeStep => exact ((origins.apply_patch _ result).erase_sandbox _).congr rfl rfl rfl
  | standalone => exact (origins.apply_patch _ result).congr rfl rfl rfl

theorem vanilla_call_origins {records : Records sig} {w after : World sig}
    {head : Head sig} {out : Option Chunk} (d : VanillaDerivation m w head after out)
    (origins : WorldOrigins records w) :
    ∀ fs, VanillaDerivation.callFS d = some fs → ∀ record ∈ fsRecords fs, record ∈ records := by
  cases d <;> intro fs same <;> cases Option.some.inj same <;> exact origins.fs

/-- Actual step collectors include no source outside these primitive maps. -/
theorem step_origins {records : Records sig} (d : StepDerivation m h executor prog)
    (before : WorldOrigins records d.before) (selected : WorldOrigins records d.selected)
    (result : ∀ record ∈ patchRecords (ProbeDerivation.result d.probe).patch, record ∈ records) :
    ∀ record ∈ d.records, record ∈ records := by
  have after : WorldOrigins records d.after := by
    cases executor with
    | incr => exact incr_after_origins d.probe selected result
    | vanilla => exact vanilla_after_origins d.probe selected result
  have call : ∀ fs, ProbeDerivation.callFS d.probe = some fs →
      ∀ record ∈ fsRecords fs, record ∈ records := by
    cases executor with
    | incr => exact incr_call_origins d.probe selected
    | vanilla => exact vanilla_call_origins d.probe selected
  have live : ∀ patch, d.livePatch = some patch →
      ∀ record ∈ patchRecords patch, record ∈ records := by
    cases executor with
    | incr => exact incr_live_origins d.probe selected result
    | vanilla =>
      intro patch same
      cases Option.some.inj same
      exact result
  intro record member
  simp only [StepDerivation.records, List.mem_append] at member
  rcases member with ((((old | chosen) | next) | patch) | called) | applied
  · exact before.records record old
  · exact selected.records record chosen
  · exact after.records record next
  · exact result record patch
  · cases fs : ProbeDerivation.callFS d.probe with
    | none => simp [fs] at called
    | some map => exact call map fs record (by simpa only [fs] using called)
  · cases patch : d.livePatch with
    | none => simp [patch] at applied
    | some map =>
      simp only [patch, List.mem_append] at applied
      rcases applied with written | scan
      · exact live map patch record written
      · exact (List.mem_append.mp (PrefixProperties.application_records_sources scan)).elim
          (selected.fs record) (live map patch record)

/-- The exact successor collector splits into the prior prefix and new step. -/
theorem records_snoc {pre next : Prefix m h executor prog start}
    {d : StepDerivation m h executor prog} (trace : next.trace = pre.trace ++ [d]) :
    next.records = pre.records ++ d.records := by
  simp only [Prefix.records, trace, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.append_assoc]

/-- A constructed isolated successor is admissible when its new patch avoids
all retained records. The result-origin premise concerns actual records,
not only content approximation. -/
theorem admissible_snoc (host : HostWellFormed m h) {witnesses : WitnessMap sig}
    {pre next : Prefix m h executor prog start} (admitted : Admissible witnesses pre)
    (d : StepDerivation m h executor prog) (trace : next.trace = pre.trace ++ [d])
    (before : d.before = pre.final) (callFresh : ProbeDerivation.Fresh d.probe)
    (isolated : Isolated next.trace) (patch : Patch sig)
    (avoid : ∀ q file, FMap.get patch q = some (.write file) →
      ∀ q' old, (q', old) ∈ pre.records ++ witnessRecords witnesses → file.mtime ≠ old.mtime)
    (result : ∀ record ∈ patchRecords (ProbeDerivation.result d.probe).patch,
      record ∈ (pre.records ++ witnessRecords witnesses) ++ patchRecords patch) :
    Admissible witnesses next := by
  let available := (pre.records ++ witnessRecords witnesses) ++ patchRecords patch
  have consistent : TimestampCompatible available :=
    C8Steps.fresh_patch_consistent _ patch
      ((pre.paperRecords_witness_consistent_iff witnesses).mp admitted.timestamps) avoid
  have prior : ∀ record ∈ pre.records, record ∈ available :=
    fun record member => List.mem_append_left _ (List.mem_append_left _ member)
  have old : WorldOrigins available d.before := by
    apply WorldOrigins.of_records
    intro record member
    rw [before] at member
    exact prior record (C8Steps.final_world_records pre record member)
  have selected : WorldOrigins available d.selected := by
    apply WorldOrigins.of_records
    intro record member
    have host' : h.select prog pre.final d.selection d.selected := by
      simpa only [before] using d.host
    exact prior record (selected_records host pre admitted.operational host' record member)
  have sources := step_origins d old selected result
  have timestamps : TimestampCompatible (next.records ++ witnessRecords witnesses) := by
    apply consistent.mono
    intro record member
    rcases List.mem_append.mp member with live | witness
    · rw [records_snoc trace] at live
      exact (List.mem_append.mp live).elim (prior record) (sources record)
    · exact List.mem_append_left _ (List.mem_append_right _ witness)
  have whole : TimestampConsistent (next.paperRecords ∪ witnessPaperRecords witnesses) :=
    (next.paperRecords_witness_consistent_iff witnesses).mpr timestamps
  refine ⟨⟨?_, TimestampConsistent.mono (fun _ member => Or.inl member) whole⟩,
    isolated, whole⟩
  intro chosen member
  rw [trace] at member
  rcases List.mem_append.mp member with previous | last
  · exact admitted.operational.fresh chosen previous
  · cases List.mem_singleton.mp last
    exact callFresh

end
end Incr.Incr.RecordInventory
