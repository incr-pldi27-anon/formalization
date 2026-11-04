import Incr.Incr.Bisimulation.Statements
import Incr.Incr.Math.PatchAlgebra
import Incr.Incr.Preservation.Components
import Incr.Incr.Preservation.Buffers
import Incr.Incr.Preservation.Cache
import Incr.Incr.Preservation.Proof
import Incr.Incr.Reuse.Boundary

/-! # `lem:paper-bisim-prefix`: whole-map provenance, timestamp records, slices,
frames, and hit paths -/

open Incr
namespace Incr.Incr

noncomputable section

variable {sig : Signature} {m : CommandModel sig} {h : Host sig}
  {executor : Executor} {prog : sig.Prog} {start : World sig}

/-- An implementation scan used only for normalized file-occurrence lemmas. -/
def applicationFilesystems (fs : FS sig) (patch : Patch sig) : List (FS sig) :=
  patch.entries.toList.scanl (fun acc kv =>
    match kv.2 with
    | .write file => acc[kv.1 ↦ file]
    | .delete => acc ∖ kv.1) fs

/-- Proof-support list; scan members are not necessarily recorded whole maps. -/
def worldFilesystems (w : World sig) : List (FS sig) :=
  [w.fs] ++ w.sandbox.entries.toList.flatMap fun kv =>
    [kv.2.base, kv.2.view] ++ applicationFilesystems kv.2.base kv.2.patch

/-- Proof-support list of whole maps, including implementation scan states. -/
def StepDerivation.filesystems (d : StepDerivation m h executor prog) : List (FS sig) :=
  worldFilesystems d.before ++ worldFilesystems d.selected ++ worldFilesystems d.after ++
    (match ProbeDerivation.callFS d.probe with | none => [] | some fs => [fs]) ++
    (match d.livePatch with
    | none => []
    | some patch => applicationFilesystems d.selected.fs patch)

/-- Normalized-proof list, not the paper's public record collection. -/
def Prefix.filesystems (pre : Prefix m h executor prog start) : List (FS sig) :=
  worldFilesystems start ++ pre.trace.flatMap StepDerivation.filesystems

/-- A proof-support enumeration of fixed initial witness filesystems. -/
def witnessFilesystems (witnesses : WitnessMap sig) : List (FS sig) :=
  witnesses.entries.toList.map fun kv => kv.2.fs

end
end Incr.Incr

namespace Incr.Incr.PrefixProperties

noncomputable section

variable {sig : Signature} {m : CommandModel sig} {h : Host sig}
  {prog : sig.Prog} {start : World sig}

theorem dom_restrict {K V : Type} (map : FMap K V) (Q : Set K) :
    FMap.dom (map ↾ Q) = FMap.dom map ∩ Q := by
  classical
  ext q
  simp only [FMap.dom, Finmap.mem_keys, Finmap.mem_iff, Set.mem_inter_iff]
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨hq, hv⟩ := (FMap.get_restrict_eq_some map Q q v).mp hv
    exact ⟨⟨v, hv⟩, hq⟩
  · rintro ⟨⟨v, hv⟩, hq⟩
    exact ⟨v, (FMap.get_restrict_eq_some map Q q v).mpr ⟨hq, hv⟩⟩

theorem dom_filterKeys {K V : Type} (map : FMap K V) (P : K → Prop)
    [DecidablePred P] : FMap.dom (FMap.filterKeys P map) = FMap.dom map ∩ {q | P q} := by
  classical
  ext q
  simp only [FMap.dom, Finmap.mem_keys, Finmap.mem_iff, Set.mem_inter_iff,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨hq, hv⟩ := (FMap.get_filterKeys_eq_some P map q v).mp hv
    exact ⟨⟨v, hv⟩, hq⟩
  · rintro ⟨⟨v, hv⟩, hq⟩
    exact ⟨v, (FMap.get_filterKeys_eq_some P map q v).mpr ⟨hq, hv⟩⟩

/-- The two live path equations imply both hit-counting equations. -/
theorem hit_accounting_of_paths {trace : Trace m h .incr prog}
    {k : Component} {sb : Sandbox sig}
    (hw : componentWrites trace k = FMap.dom sb.patch)
    (ha : componentAccesses trace k =
      FMap.dom sb.patch ∪ FMap.dom sb.reads ∪ FMap.dom sb.writes) :
    HitPathAccounting trace k sb := by
  intro d dm r rm w wm hp hr hw'
  have hd := hp.1
  rw [FMap.dom_merge] at hd
  rw [hw, ha, hd, hr, hw', FMap.dom_merge, FMap.dom_merge,
    dom_restrict, dom_restrict]
  constructor <;> ext q <;> simp only [Set.mem_union, Set.mem_inter_iff,
    Set.mem_sdiff, Set.mem_univ, true_and] <;> tauto

def historyWrites (trace : Trace m h .incr prog) : Set sig.Path :=
  {q | ∃ d ∈ trace, q ∈ FMap.dom (ProbeDerivation.result d.probe).patch}

def historyAccesses (trace : Trace m h .incr prog) : Set sig.Path :=
  {q | ∃ d ∈ trace,
    q ∈ FMap.dom (ProbeDerivation.result d.probe).patch ∪
      FMap.dom (ProbeDerivation.result d.probe).reads ∪
      FMap.dom (ProbeDerivation.result d.probe).writes}

theorem historyWrites_snoc (trace : Trace m h .incr prog)
    (d : StepDerivation m h .incr prog) :
    historyWrites (trace ++ [d]) =
      historyWrites trace ∪ FMap.dom (ProbeDerivation.result d.probe).patch := by
  ext q
  simp only [historyWrites, Set.mem_ofPred_eq, List.mem_append, List.mem_singleton,
    Set.mem_union]
  aesop

theorem historyAccesses_snoc (trace : Trace m h .incr prog)
    (d : StepDerivation m h .incr prog) :
    historyAccesses (trace ++ [d]) = historyAccesses trace ∪
      FMap.dom (ProbeDerivation.result d.probe).patch ∪
      FMap.dom (ProbeDerivation.result d.probe).reads ∪
      FMap.dom (ProbeDerivation.result d.probe).writes := by
  ext q
  simp only [historyAccesses, Set.mem_ofPred_eq, List.mem_append, List.mem_singleton,
    Set.mem_union]
  aesop

/-- Exact history accumulation gives the path sets, including discarded dependencies. -/
theorem accumulation_paths {base : FS sig} {trace : Trace m h .incr prog}
    {sb : Sandbox sig} (acc : HistoryAccumulation base trace sb) :
    historyWrites trace = FMap.dom sb.patch ∧
      historyAccesses trace = FMap.dom sb.patch ∪ FMap.dom sb.reads ∪ FMap.dom sb.writes := by
  induction acc with
  | nil => simp [historyWrites, historyAccesses, Sandbox.initial]
  | snoc trace sb d previous hi ho hopen ih =>
    rw [historyWrites_snoc, historyAccesses_snoc, ih.1, ih.2]
    simp only [Sandbox.accumulate, FMap.dom_merge, dom_filterKeys]
    constructor
    · trivial
    · ext q
      simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq, FMap.dom]
      tauto

/-- No close in a component means every retained step contributes to its open history. -/
theorem openHistory_eq_componentSteps {trace : Trace m h .incr prog} {entry i : Nat}
    (live : ¬ slotClosed trace entry i) :
    openHistory trace (.pipeline entry i) = componentSteps trace (.pipeline entry i) := by
  apply List.filter_eq_self.mpr
  intro d hd
  have notClosed : (ProbeDerivation.input d.probe).flag ≠ .eof := by
    intro he
    exact live ⟨d, hd, he⟩
  cases hf : (ProbeDerivation.input d.probe).flag <;> simp_all

/-- The `lem:paper-buffers` history and live-domain clauses imply both
`lem:paper-bisim-prefix` path equations. -/
theorem live_paths {trace : Trace m h .incr prog} {world : World sig}
    (state : SandboxState trace world) {i : Nat} {sb : Sandbox sig}
    (hs : FMap.get world.sandbox i = some sb) :
    ∃ entry init, latestPipeline trace = some (entry, init) ∧
      componentWrites trace (.pipeline entry i) = FMap.dom sb.patch ∧
      componentAccesses trace (.pipeline entry i) =
        FMap.dom sb.patch ∪ FMap.dom sb.reads ∪ FMap.dom sb.writes := by
  obtain ⟨entry, init, entryStep, latest, _, _, _, acc⟩ := state.2.1 i sb hs
  have present : i ∈ FMap.dom world.sandbox :=
    Finmap.mem_keys.mpr (Finmap.mem_iff.mpr ⟨sb, hs⟩)
  have notClosed := ((state.2.2.2.1 entry init latest i).mp present).2
  change HistoryAccumulation sb.base (openHistory trace (.pipeline entry i)) sb at acc
  rw [openHistory_eq_componentSteps notClosed] at acc
  obtain ⟨hw, ha⟩ := accumulation_paths acc
  refine ⟨entry, init, latest, hw, ?_⟩
  rw [← ha]
  ext q
  simp only [componentAccesses, componentDeps, componentWrites, historyAccesses,
    Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · rintro (⟨d, hd, hr | hw⟩ | ⟨d, hd, hp⟩)
    · exact ⟨d, hd, Or.inl (Or.inr hr)⟩
    · exact ⟨d, hd, Or.inr hw⟩
    · exact ⟨d, hd, Or.inl (Or.inl hp)⟩
  · rintro ⟨d, hd, (hp | hr) | hw⟩
    · exact Or.inr ⟨d, hd, hp⟩
    · exact Or.inl ⟨d, hd, Or.inl hr⟩
    · exact Or.inl ⟨d, hd, Or.inr hw⟩

/-- A lookup in an actual patch scan comes from its initial map or a scanned write. -/
theorem scan_lookup_sources
    (entries : List (Sigma fun _ : sig.Path => Edit sig)) (fs : FS sig)
    {snapshot : FS sig} {q : sig.Path} {file : File sig}
    (hs : snapshot ∈ entries.scanl (fun acc kv =>
      match kv.2 with
      | .write f => acc[kv.1 ↦ f]
      | .delete => acc ∖ kv.1) fs)
    (lookup : FMap.get snapshot q = some file) :
    FMap.get fs q = some file ∨ (⟨q, .write file⟩ : Sigma fun _ : sig.Path => Edit sig) ∈ entries := by
  classical
  induction entries generalizing fs with
  | nil =>
    simp only [List.scanl_nil, List.mem_singleton] at hs
    subst snapshot
    exact Or.inl lookup
  | cons kv rest ih =>
    simp only [List.scanl_cons, List.mem_cons] at hs
    rcases hs with rfl | hs
    · exact Or.inl lookup
    · rcases ih _ hs with origin | inserted
      · cases kv with
        | mk key edit =>
          cases edit with
          | write newFile =>
            by_cases hq : q = key
            · subst key
              rw [FMap.get_set_self] at origin
              cases Option.some.inj origin
              exact Or.inr (List.mem_cons_self)
            · exact Or.inl (by simpa only [FMap.get_set_other hq] using origin)
          | delete =>
            by_cases hq : q = key
            · subst key
              simp only [FMap.get_erase_self] at origin
              contradiction
            · exact Or.inl (by simpa only [FMap.get_erase_of_ne hq] using origin)
      · exact Or.inr (List.mem_cons_of_mem _ inserted)

/-- Every whole-map record from an application scan contributes its actual file records. -/
theorem application_record_membership {fs snapshot : FS sig} {patch : Patch sig}
    (hs : snapshot ∈ applicationFilesystems fs patch) {record : sig.Path × File sig}
    (hr : record ∈ fsRecords snapshot) : record ∈ applicationRecords fs patch := by
  exact List.mem_flatMap.mpr ⟨snapshot, hs, hr⟩

/-- Files in a scan are already accounted for by the base and patch records. -/
theorem application_records_sources {fs : FS sig} {patch : Patch sig}
    {record : sig.Path × File sig} (hr : record ∈ applicationRecords fs patch) :
    record ∈ fsRecords fs ++ patchRecords patch := by
  obtain ⟨snapshot, hs, hm⟩ := List.mem_flatMap.mp hr
  rcases scan_lookup_sources patch.entries.toList fs hs (get_of_mem_fsRecords hm) with base | write
  · exact List.mem_append_left _ (mem_fsRecords_of_get base)
  · apply List.mem_append_right
    apply List.mem_filterMap.mpr
    exact ⟨⟨record.1, .write record.2⟩, write, rfl⟩

/-- The computed view's lookup comes from the base or a patch write. -/
theorem view_record_sources {fs : FS sig} {patch : Patch sig}
    {record : sig.Path × File sig} (hr : record ∈ fsRecords (applyPatch fs patch)) :
    record ∈ fsRecords fs ++ patchRecords patch := by
  classical
  have hv := get_of_mem_fsRecords hr
  cases he : FMap.get patch record.1 with
  | none =>
    rw [Incr.applyPatch_get_none he] at hv
    exact List.mem_append_left _ (mem_fsRecords_of_get hv)
  | some edit =>
    cases edit with
    | delete =>
      rw [Incr.applyPatch_get_delete he] at hv
      contradiction
    | write file =>
      rw [Incr.applyPatch_get_write he] at hv
      cases Option.some.inj hv
      apply List.mem_append_right
      apply List.mem_filterMap.mpr
      exact ⟨⟨record.1, .write record.2⟩,
        Multiset.mem_toList.mpr (Finmap.lookup_eq_some_iff.mp he), rfl⟩

/-- Whole-map membership in a world implies flattened record membership. -/
theorem world_record_membership {world : World sig} {snapshot : FS sig}
    (hs : snapshot ∈ worldFilesystems world) {record : sig.Path × File sig}
    (hr : record ∈ fsRecords snapshot) : record ∈ worldRecords world := by
  simp only [worldFilesystems, List.mem_append, List.mem_singleton, List.mem_flatMap] at hs
  rcases hs with rfl | ⟨kv, hkv, hs⟩
  · exact List.mem_append_left _ (List.mem_append_left _ hr)
  · apply List.mem_append_right
    apply List.mem_flatMap.mpr
    refine ⟨kv, hkv, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with (rfl | rfl) | hs
    · exact List.mem_append_left _ (List.mem_append_left _ hr)
    · exact List.mem_append_left _ (view_record_sources hr)
    · exact List.mem_append_right _ (application_record_membership hs hr)

/-- Whole maps retained by a step retain every corresponding path/file record. -/
theorem step_record_membership {d : StepDerivation m h .incr prog} {snapshot : FS sig}
    (hs : snapshot ∈ d.filesystems) {record : sig.Path × File sig}
    (hr : record ∈ fsRecords snapshot) : record ∈ d.records := by
  simp only [StepDerivation.filesystems, List.mem_append] at hs
  rcases hs with (((hs | hs) | hs) | hs) | hs
  · have hm := world_record_membership hs hr
    simp only [StepDerivation.records, List.mem_append]
    tauto
  · have hm := world_record_membership hs hr
    simp only [StepDerivation.records, List.mem_append]
    tauto
  · have hm := world_record_membership hs hr
    simp only [StepDerivation.records, List.mem_append]
    tauto
  · cases hc : ProbeDerivation.callFS d.probe with
    | none => simp [hc] at hs
    | some callFS =>
      simp only [hc, List.mem_singleton] at hs
      subst snapshot
      simp only [StepDerivation.records, hc, List.mem_append]
      tauto
  · cases hp : d.livePatch with
    | none => simp [hp] at hs
    | some patch =>
      simp only [hp] at hs
      have hm := application_record_membership hs hr
      simp only [StepDerivation.records, hp, List.mem_append]
      tauto

/-- Whole-filesystem prefix provenance implies actual flattened-record provenance. -/
theorem prefix_record_membership {pre : Prefix m h .incr prog start} {snapshot : FS sig}
    (hs : snapshot ∈ pre.filesystems) {record : sig.Path × File sig}
    (hr : record ∈ fsRecords snapshot) : record ∈ pre.records := by
  rcases List.mem_append.mp hs with hs | hs
  · exact List.mem_append_left _ (world_record_membership hs hr)
  · obtain ⟨d, hd, hs⟩ := List.mem_flatMap.mp hs
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨d, hd, step_record_membership hs hr⟩)

/-- A fixed witness's filesystem contributes all its actual file records. -/
theorem witness_record_membership {witnesses : WitnessMap sig} {snapshot : FS sig}
    (hs : snapshot ∈ witnessFilesystems witnesses) {record : sig.Path × File sig}
    (hr : record ∈ fsRecords snapshot) : record ∈ witnessRecords witnesses := by
  obtain ⟨kv, hkv, rfl⟩ := List.mem_map.mp hs
  exact List.mem_flatMap.mpr ⟨kv, hkv, hr⟩

/-- Admissibility supplies timestamp compatibility for either source of whole-map provenance. -/
theorem provenance_timestamps {witnesses : WitnessMap sig}
    {pre : Prefix m h .incr prog start} (admitted : Admissible witnesses pre)
    {snapshot : FS sig}
    (source : recordOfFS snapshot ∈ witnessPaperRecords witnesses ∨
      recordOfFS snapshot ∈ pre.paperRecords) :
    TimestampConsistent (pre.paperRecords ∪ {recordOfFS snapshot}) := by
  apply TimestampConsistent.mono ?_ admitted.timestamps
  intro record member
  rcases member with old | singleton
  · exact Or.inl old
  · have same : record = recordOfFS snapshot := Set.mem_singleton_iff.mp singleton
    subst record
    exact source.elim Or.inr Or.inl

/-- Cache certificates retain the full filesystem that supplied the denotation. -/
def WitnessedCache (cache : Cache sig) (sources : Set (FS sig)) : Prop :=
  ∀ key memo, FMap.get cache key = some memo →
    ∃ (p : sig.Probe) (env : Env sig) (input : Chunk) (fs : FS sig),
      Cacheable m p ∧ input.flag = .eof ∧ key = cacheKey m p env input ∧
      m.denotes p input fs env memo.result ∧ fs ∈ sources

theorem WitnessedCache.mono {cache : Cache sig} {sources sources' : Set (FS sig)}
    (wf : WitnessedCache (m := m) cache sources) (sub : sources ⊆ sources') :
    WitnessedCache (m := m) cache sources' := by
  intro key memo hm
  obtain ⟨p, env, input, fs, hc, he, hk, hd, hs⟩ := wf key memo hm
  exact ⟨p, env, input, fs, hc, he, hk, hd, sub hs⟩

theorem witnessed_cache_insert {cache : Cache sig} {sources : Set (FS sig)}
    (wf : WitnessedCache (m := m) cache sources)
    {p : sig.Probe} {env : Env sig} {input : Chunk} {fs : FS sig} {memo : Memo sig}
    (hc : Cacheable m p) (he : input.flag = .eof)
    (hd : m.denotes p input fs env memo.result) (hs : fs ∈ sources) :
    WitnessedCache (m := m) (FMap.set cache (cacheKey m p env input) memo) sources := by
  classical
  intro key value hv
  by_cases hk : key = cacheKey m p env input
  · subst key
    rw [FMap.get_set_self] at hv
    cases Option.some.inj hv
    exact ⟨p, env, input, fs, hc, he, rfl, hd, hs⟩
  · rw [FMap.get_set_other hk] at hv
    exact wf key value hv

/-- Raw insertion uses its actual base, never an unrelated `def:paper-cache-wf`
witness. -/
theorem raw_cache_provenance {before after : World sig} {head : Head sig} {out : Option Chunk}
    {sources : Set (FS sig)} (wf : WitnessedCache (m := m) before.cache sources)
    (live : before.fs ∈ sources)
    (bases : ∀ i sb, FMap.get before.sandbox i = some sb → sb.base ∈ sources)
    (folds : ∀ (p : sig.Probe) (i : Nat) (sb : Sandbox sig),
      head = .pipeline p i → FMap.get before.sandbox i = some sb → Cacheable m p →
      ∀ (input : Chunk) (result : Result sig)
        (hi : sb.input.flag = .open) (ho : sb.output.flag = .open),
        m.denotes p input sb.view before.env result →
        m.denotes p (Chunk.concat sb.input input hi) sb.base before.env
          (combineResults (sandboxResult sb) result ho))
    (derivation : IncrDerivation m before head after out) :
    WitnessedCache (m := m) after.cache sources := by
  cases derivation with
  | pipelineOpen => exact wf
  | uncacheClose => exact wf
  | cacheCloseHit => exact wf
  | uncacheStandalone => exact wf
  | cacheStandaloneHit => exact wf
  | cacheCloseMiss p i sb s r es buffers out hc hb hs hi ho hm call hstatus hf hp =>
    apply witnessed_cache_insert (fs := sb.base) wf hc rfl
    · change m.denotes p (sb.input ++'hi ⟨s, .eof⟩) sb.base before.env
        (accumulatedMemo sb ⟨s, .eof⟩ r es hi ho hf).result
      rw [CachePrefixes.accumulated_memo_result sb _ r es hi ho hf hstatus]
      exact folds p i sb rfl hs hc _ r hi ho call
    · exact bases i sb hs
  | cacheStandaloneMiss p s r es hc hin hm call hstatus hf =>
    apply witnessed_cache_insert (fs := before.fs) wf hc rfl
    · convert call using 1
      cases r
      simp only at hstatus
      subst_vars
      rfl
    · exact live

def provenanceSources (witnesses : WitnessMap sig) (initial : World sig)
    (trace : Trace m h .incr prog) : Set (FS sig) :=
  {fs | recordOfFS fs ∈ witnessPaperRecords witnesses ∨
    recordOfFS fs ∈ worldPaperRecords initial ∪
      {record | ∃ d ∈ trace, record ∈ d.paperRecords}}

theorem provenanceSources_snoc {witnesses : WitnessMap sig} {initial : World sig}
    {trace : Trace m h .incr prog} {d : StepDerivation m h .incr prog} :
    provenanceSources witnesses initial trace ⊆ provenanceSources witnesses initial (trace ++ [d]) := by
  intro fs hs
  rcases hs with initialWitness | initialWorld | ⟨step, member, record⟩
  · exact Or.inl initialWitness
  · exact Or.inr (Or.inl initialWorld)
  · exact Or.inr (Or.inr ⟨step, List.mem_append_left _ member, record⟩)

theorem selected_source {witnesses : WitnessMap sig} {initial : World sig}
    {trace : Trace m h .incr prog} {d : StepDerivation m h .incr prog}
    {fs : FS sig} (hs : recordOfFS fs ∈ worldPaperRecords d.selected) :
    fs ∈ provenanceSources witnesses initial (trace ++ [d]) := by
  apply Or.inr
  apply Or.inr
  refine ⟨d, by simp, ?_⟩
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hs))))

theorem base_in_world {world : World sig} {i : Nat} {sb : Sandbox sig}
    (hs : FMap.get world.sandbox i = some sb) : sb.base ∈ worldFilesystems world := by
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨⟨i, sb⟩, Multiset.mem_toList.mpr (Finmap.lookup_eq_some_iff.mp hs), ?_⟩
  simp

/-- Prefix provenance for every current memo, including all cache insertions. -/
theorem cache_provenance (shape : DenotationShape m) (commands : WellFormedCommands m)
    (key : HashInjective m) (host : HostWellFormed m h)
    (cache : WellFormedCache m start.cache) (witnesses : WitnessMap sig)
    (witnessed : WitnessesFor m start.cache witnesses)
    (pre : Prefix m h .incr prog start) (operational : Operational pre) :
    WitnessedCache (m := m) pre.final.cache (provenanceSources witnesses start pre.trace) := by
  apply operational.trace_induction (fun trace world =>
    WitnessedCache (m := m) world.cache (provenanceSources witnesses start trace))
  · intro key memo hm
    obtain ⟨witness, hw, p, env, hc, he, hk, hd⟩ := witnessed.2 key memo hm
    exact ⟨p, env, witness.input, witness.fs, hc, he, hk, hd,
      Or.inl ⟨key, witness, hw, rfl⟩⟩
  · intro earlier op ih d he
    have chosen : h.select prog earlier.final d.selection d.selected := by
      simpa only [he] using d.host
    have discipline := host.selectionDiscipline .incr prog start earlier op _ _ chosen
    have current : WitnessedCache (m := m) d.selected.cache
        (provenanceSources witnesses start (earlier.trace ++ [d])) := by
      rw [discipline.2.2.1]
      exact ih.mono provenanceSources_snoc
    apply raw_cache_provenance current
    · exact selected_source (world_fs_mem_paperRecords d.selected)
    · intro i sb hs
      exact selected_source (sandbox_mem_paperRecords hs).1
    · intro p i sb hh hs hc input result hi ho call
      have state := (buffer_sandbox_preservation shape commands key host earlier op).1
      have prefixes := (cacheable_prefixes shape commands key host cache earlier op).2.1
      rcases hit_selected_prefix_cases op host state prefixes chosen hh hs hc with initial | denoted
      · have call' : m.denotes p input (Sandbox.initial sb.base).view d.selected.env result := by
          simpa only [← initial] using call
        convert CachePrefixes.fold_initial call' using 1 <;> simp only [← initial]
      · exact CachePrefixes.fold_progressed commands hc hi ho denoted call
    · exact d.probe

/-- `lem:paper-bisim-prefix` clause (i), with actual whole-map provenance and
`def:paper-timestamps` timestamp compatibility. -/
theorem prefix_cache_witnesses (shape : DenotationShape m) (commands : WellFormedCommands m)
    (key : HashInjective m) (host : HostWellFormed m h)
    (cache : WellFormedCache m start.cache) (witnesses : WitnessMap sig)
    (witnessed : WitnessesFor m start.cache witnesses)
    (pre : Prefix m h .incr prog start) (admitted : Admissible witnesses pre) :
    PrefixCacheWitnesses witnesses pre := by
  intro key' memo hm
  obtain ⟨p, env, input, fs, hc, he, hk, hd, hs⟩ :=
    cache_provenance shape commands key host cache witnesses witnessed pre admitted.operational key' memo hm
  have source : recordOfFS fs ∈ witnessPaperRecords witnesses ∨ recordOfFS fs ∈ pre.paperRecords := hs
  exact ⟨p, env, ⟨input, fs⟩, hc, he, hk, hd, source, provenance_timestamps admitted source⟩

def FrameAt (trace : Trace m h .incr prog) (world : World sig)
    (entry i : Nat) (sb : Sandbox sig) : Prop :=
  ∀ Q : Set sig.Path, Disjoint Q (otherWrites trace entry i) → sb.base ↾ Q = world.fs ↾ Q

def LiveFrames (trace : Trace m h .incr prog) (world : World sig)
    (current : Option (Nat × PipelineInit sig)) : Prop :=
  ∀ i sb, FMap.get world.sandbox i = some sb →
    ∃ entry init, current = some (entry, init) ∧ FrameAt trace world entry i sb

/-- `lem:paper-buffers` supplies the path clauses; a filesystem frame supplies the
remaining clause. -/
theorem live_slices_of_frames {trace : Trace m h .incr prog} {world : World sig}
    (state : SandboxState trace world) (frames : LiveFrames trace world (latestPipeline trace)) :
    LiveSliceProperties trace world (latestPipeline trace) := by
  intro i sb hs
  obtain ⟨entry, init, hl, hw, ha⟩ := live_paths state hs
  obtain ⟨entry', init', hl', frame⟩ := frames i sb hs
  have eqs := Option.some.inj (hl.symm.trans hl')
  cases eqs
  exact ⟨entry, init, hl, ⟨hw, ha, frame⟩, hit_accounting_of_paths hw ha⟩

/-- Selection preserves every live slice and establishes all newly initialized slices. -/
theorem selection_slices {trace : Trace m h .incr prog} {before selected : World sig}
    {selection : Selection sig} (hd : SelectionDiscipline trace before selection selected)
    (slices : LiveSliceProperties trace before (latestPipeline trace)) :
    LiveSliceProperties trace selected (selectedPipeline trace selection) := by
  intro i sb hs
  cases hi : selection.init with
  | none =>
    have hm : selected.sandbox = before.sandbox := by
      have hinit := hd.2.2.2.1
      simp only [hi] at hinit
      exact hinit.1
    obtain ⟨entry, init, hl, slice, hit⟩ := slices i sb (by simpa only [hm] using hs)
    refine ⟨entry, init, ?_, ?_, hit⟩
    · simpa only [selectedPipeline, hi] using hl
    · exact ⟨slice.1, slice.2.1, by simpa only [hd.1] using slice.2.2⟩
  | some init =>
    have hm : selected.sandbox = initialSandboxes init before.fs := by
      have hinit := hd.2.2.2.1
      simp only [hi] at hinit
      exact hinit.2.2.2.2
    have hb := initialSandboxes_get_eq init before.fs (by simpa only [hm] using hs)
    subst sb
    have hz := componentSteps_future_entry trace (entry := trace.length) i (by omega)
    have hw : componentWrites trace (.pipeline trace.length i) =
        FMap.dom (Sandbox.initial before.fs).patch := by
      simp [componentWrites, hz, Sandbox.initial]
    have ha : componentAccesses trace (.pipeline trace.length i) =
        FMap.dom (Sandbox.initial before.fs).patch ∪
        FMap.dom (Sandbox.initial before.fs).reads ∪ FMap.dom (Sandbox.initial before.fs).writes := by
      simp [componentAccesses, componentDeps, componentWrites, hz, Sandbox.initial]
    refine ⟨trace.length, init, by simp [selectedPipeline, hi], ?_, hit_accounting_of_paths hw ha⟩
    exact ⟨hw, ha, by simp [Sandbox.initial, hd.1]⟩

theorem componentWrites_mono_snoc (trace : Trace m h .incr prog)
    (d : StepDerivation m h .incr prog) (k : Component) :
    componentWrites trace k ⊆ componentWrites (trace ++ [d]) k := by
  rintro q ⟨e, he, hq⟩
  exact ⟨e, by rw [componentSteps_snoc]; exact List.mem_append_left _ he, hq⟩

theorem result_writes_in_component {trace : Trace m h .incr prog}
    {d : StepDerivation m h .incr prog} {k : Component}
    (hk : componentAt (trace ++ [d]) trace.length d = some k) :
    FMap.dom (ProbeDerivation.result d.probe).patch ⊆ componentWrites (trace ++ [d]) k := by
  intro q hq
  exact ⟨d, by rw [componentSteps_snoc]; simp [hk], hq⟩

theorem mem_otherWrites {trace : Trace m h .incr prog} {entry i : Nat} {q : sig.Path} :
    q ∈ otherWrites trace entry i ↔ ∃ j, j ≠ i ∧ q ∈ componentWrites trace (.pipeline entry j) := by
  simp [otherWrites]

theorem otherWrites_mono_snoc (trace : Trace m h .incr prog)
    (d : StepDerivation m h .incr prog) (entry i : Nat) :
    otherWrites trace entry i ⊆ otherWrites (trace ++ [d]) entry i := by
  intro q hq
  obtain ⟨j, hj, hq⟩ := mem_otherWrites.mp hq
  exact mem_otherWrites.mpr ⟨j, hj, componentWrites_mono_snoc trace d _ hq⟩

/-- Applying a patch outside a queried set preserves the exact restricted map. -/
theorem patch_restrict_frame (fs : FS sig) (patch : Patch sig) (Q : Set sig.Path)
    (hd : Disjoint Q (FMap.dom patch)) : (applyPatch fs patch) ↾ Q = fs ↾ Q := by
  classical
  apply FMap.restrict_congr
  intro q hq
  apply Incr.applyPatch_get_none
  apply FMap.get_eq_none.mpr
  intro hm
  exact Set.disjoint_left.mp hd hq (Finmap.mem_keys.mpr hm)

/-- A local write-support proof transports the live frames across one raw step. -/
theorem frame_update {trace : Trace m h .incr prog} {d : StepDerivation m h .incr prog}
    (slices : LiveSliceProperties trace d.selected (selectedPipeline trace d.selection))
    (patch : Patch sig) (fs : d.after.fs = applyPatch d.selected.fs patch)
    (maps : ∀ i sb, FMap.get d.after.sandbox i = some sb →
      ∃ old, FMap.get d.selected.sandbox i = some old ∧ sb.base = old.base)
    (support : ∀ i sb entry init, FMap.get d.after.sandbox i = some sb →
      selectedPipeline trace d.selection = some (entry, init) →
      FMap.dom patch ⊆ otherWrites (trace ++ [d]) entry i) :
    LiveFrames (trace ++ [d]) d.after (latestPipeline (trace ++ [d])) := by
  intro i sb hs
  obtain ⟨old, hold, hb⟩ := maps i sb hs
  obtain ⟨entry, init, latest, slice, _⟩ := slices i old hold
  refine ⟨entry, init, by simpa only [latestPipeline_snoc] using latest, ?_⟩
  intro Q hd
  have hdold : Disjoint Q (otherWrites trace entry i) :=
    hd.mono_right (otherWrites_mono_snoc trace d entry i)
  have hpatch : Disjoint Q (FMap.dom patch) := hd.mono_right (support i sb entry init hs latest)
  rw [hb, slice.2.2 Q hdold, fs, patch_restrict_frame _ _ _ hpatch]

/-- A close's staged writes and closing result belong to its cumulative component writes. -/
theorem closing_support {trace : Trace m h .incr prog} {d : StepDerivation m h .incr prog}
    (slices : LiveSliceProperties trace d.selected (selectedPipeline trace d.selection))
    {p : sig.Probe} {j : Nat} {old : Sandbox sig}
    (head : d.selection.head = .pipeline p j)
    (hs : FMap.get d.selected.sandbox j = some old)
    {patch : Patch sig}
    (bound : FMap.dom patch ⊆ FMap.dom old.patch ∪ FMap.dom (ProbeDerivation.result d.probe).patch)
    {i : Nat} (hne : i ≠ j) {entry : Nat} {init : PipelineInit sig}
    (latest : selectedPipeline trace d.selection = some (entry, init)) :
    FMap.dom patch ⊆ otherWrites (trace ++ [d]) entry i := by
  obtain ⟨entry', init', latest', slice, _⟩ := slices j old hs
  have eqs := Option.some.inj (latest.symm.trans latest')
  cases eqs
  have component : componentAt (trace ++ [d]) trace.length d = some (.pipeline entry j) := by
    rw [componentAt_snoc_last, head]
    simp only [selectedComponent, latest, Option.map_some]
  intro q hq
  apply mem_otherWrites.mpr
  refine ⟨j, Ne.symm hne, ?_⟩
  rcases bound hq with hq | hq
  · apply componentWrites_mono_snoc trace d
    rw [slice.1]
    exact hq
  · exact result_writes_in_component component hq

theorem open_frame_update {trace : Trace m h .incr prog} {d : StepDerivation m h .incr prog}
    (slices : LiveSliceProperties trace d.selected (selectedPipeline trace d.selection))
    {j : Nat} {old : Sandbox sig} {input : Chunk} {result : Result sig}
    (hs : FMap.get d.selected.sandbox j = some old)
    (hi : old.input.flag = .open) (ho : old.output.flag = .open)
    (maps : d.after.sandbox = d.selected.sandbox[j ↦ (old.accumulate input result hi ho)])
    (fs : d.after.fs = d.selected.fs) :
    LiveFrames (trace ++ [d]) d.after (latestPipeline (trace ++ [d])) := by
  apply frame_update slices (∅ : Patch sig)
  · simpa only [Incr.applyPatch_empty] using fs
  · intro i sb hsb
    rw [maps] at hsb
    by_cases hij : i = j
    · subst i
      rw [FMap.get_set_self] at hsb
      cases Option.some.inj hsb
      exact ⟨old, hs, rfl⟩
    · rw [FMap.get_set_other hij] at hsb
      exact ⟨sb, hsb, rfl⟩
  · intro i sb entry init hsb latest
    simp

theorem close_frame_update {trace : Trace m h .incr prog} {d : StepDerivation m h .incr prog}
    (slices : LiveSliceProperties trace d.selected (selectedPipeline trace d.selection))
    {p : sig.Probe} {j : Nat} {old : Sandbox sig}
    (head : d.selection.head = .pipeline p j)
    (hs : FMap.get d.selected.sandbox j = some old)
    {patch : Patch sig} (fs : d.after.fs = applyPatch d.selected.fs patch)
    (maps : d.after.sandbox = d.selected.sandbox ∖ j)
    (bound : FMap.dom patch ⊆ FMap.dom old.patch ∪ FMap.dom (ProbeDerivation.result d.probe).patch) :
    LiveFrames (trace ++ [d]) d.after (latestPipeline (trace ++ [d])) := by
  have surviving : ∀ i sb, FMap.get d.after.sandbox i = some sb → i ≠ j := by
    intro i sb hsb hij
    subst i
    rw [maps, FMap.get_erase_self] at hsb
    contradiction
  apply frame_update slices patch fs
  · intro i sb hsb
    have hij := surviving i sb hsb
    rw [maps, FMap.get_erase_of_ne hij] at hsb
    exact ⟨sb, hsb, rfl⟩
  · intro i sb entry init hsb latest
    exact closing_support slices head hs bound (surviving i sb hsb) latest

theorem standalone_frames {trace : Trace m h .incr prog} {d : StepDerivation m h .incr prog}
    (discipline : SelectionDiscipline trace d.before d.selection d.selected)
    {p : sig.Probe} (head : d.selection.head = .standalone p)
    (maps : d.after.sandbox = d.selected.sandbox) :
    LiveFrames (trace ++ [d]) d.after (latestPipeline (trace ++ [d])) := by
  have standalone := discipline.2.2.2.2
  rw [head] at standalone
  have hempty := standalone.2.2.2.2.1
  intro i sb hs
  rw [maps, hempty] at hs
  simp [FMap.get] at hs

/-- Every raw rule preserves frames; closes account for closed components too. -/
theorem raw_frames {trace : Trace m h .incr prog} (d : StepDerivation m h .incr prog)
    (discipline : SelectionDiscipline trace d.before d.selection d.selected)
    (slices : LiveSliceProperties trace d.selected (selectedPipeline trace d.selection)) :
    LiveFrames (trace ++ [d]) d.after (latestPipeline (trace ++ [d])) := by
  cases d with
  | mk before sel selected after out host probe =>
    cases sel with
    | mk head init delivery =>
      cases probe with
      | pipelineOpen p j sb taken remaining r buffers returned hb hs hi ho call hstatus hflag hp =>
        exact open_frame_update slices hs hi ho rfl (applyPatch_empty selected.fs)
      | uncacheClose p j sb s r es buffers returned hc hb hs call hstatus hflag hp =>
        apply close_frame_update slices rfl hs rfl rfl
        simp only [FMap.dom_merge, ProbeDerivation.result, IncrDerivation.result]
        exact Set.Subset.rfl
      | cacheCloseMiss p j sb s r es buffers returned hc hb hs hi ho hm call hstatus hflag hp =>
        apply close_frame_update slices rfl hs rfl rfl
        simp only [FMap.dom_merge, ProbeDerivation.result, IncrDerivation.result]
        exact Set.Subset.rfl
      | cacheCloseHit p j sb s tail memo buffers returned hc hb hs hi ho hm hv hg hp =>
        apply close_frame_update slices rfl hs rfl rfl
        simp only [ProbeDerivation.result, IncrDerivation.result, Memo.result]
        exact Set.subset_union_right
      | uncacheStandalone => exact standalone_frames discipline rfl rfl
      | cacheStandaloneMiss => exact standalone_frames discipline rfl rfl
      | cacheStandaloneHit => exact standalone_frames discipline rfl rfl

/-- Operational prefix induction preserves exact frames against all other closes. -/
theorem live_frames (shape : DenotationShape m) (commands : WellFormedCommands m)
    (key : HashInjective m) (host : HostWellFormed m h)
    (pre : Prefix m h .incr prog start) (operational : Operational pre) :
    LiveFrames pre.trace pre.final (latestPipeline pre.trace) := by
  apply operational.trace_induction (fun trace world => LiveFrames trace world (latestPipeline trace))
  · intro i sb hs
    rw [pre.initial.2.1] at hs
    simp [FMap.get] at hs
  · intro earlier op ih d he
    have discipline := host.selectionDiscipline .incr prog start earlier op
      d.selection d.selected (by simpa only [he] using d.host)
    have state := (buffer_sandbox_preservation shape commands key host earlier op).1
    have slices := selection_slices discipline (live_slices_of_frames state ih)
    exact raw_frames d (by simpa only [he] using discipline) slices

/-- `lem:paper-bisim-prefix`, with the exact production signature and no
dependency on the later bisimulation or soundness results. -/
theorem paper_bisim_prefix (_shape : DenotationShape m)
    (_commands : WellFormedCommands m) (_key : HashInjective m)
    (_host : HostWellFormed m h) (_cache : WellFormedCache m start.cache)
    (witnesses : WitnessMap sig) (_witnesses : WitnessesFor m start.cache witnesses)
    (_initialRecords : TimestampConsistent (worldPaperRecords start ∪ witnessPaperRecords witnesses))
    (pre : Prefix m h .incr prog start) (_admissible : Admissible witnesses pre) :
    BisimPrefixProperties witnesses pre := by
  have frames := live_frames _shape _commands _key _host pre _admissible.operational
  have state := (buffer_sandbox_preservation _shape _commands _key _host pre
    _admissible.operational).1
  have slices := live_slices_of_frames state frames
  refine ⟨prefix_cache_witnesses _shape _commands _key _host _cache witnesses _witnesses pre
    _admissible, slices, ?_⟩
  intro selection selected chosen
  exact selection_slices (_host.selectionDiscipline .incr prog start pre
    _admissible.operational selection selected chosen) slices

end

end Incr.Incr.PrefixProperties



