import Incr.IncrPP.Preservation.Statements

/-!
# E.6 support: repair bases, denotation folds, and cache provenance

Next calls are denotations, not assumed operational continuations (G2).
The entry package is separate from global cache/provenance conclusions (G1).
-/
namespace Incr.IncrPP

open Incr
noncomputable section
variable {sig : Signature} {m : CommandModel sig} {h : Host sig}
  {prog : sig.Prog} {start : World sig}

/-- The proof-only preimage patch restores a record or explicit absence on D. -/
def prePatch (fs : FS sig) (paths : Finset sig.Path) : Patch sig :=
  (paths.toList.map fun q => (⟨q, match FMap.get fs q with
    | some file => Edit.write file
    | none => .delete⟩ : Sigma (fun _ : sig.Path => Edit sig))).toFinmap

/-- The unnumbered absorption identity immediately before E.6. -/
theorem patch_absorption (fs : FS sig) (first last : Patch sig)
    (covered : FMap.dom first ⊆ FMap.dom last) :
    applyPatch (applyPatch fs first) last = applyPatch fs last := by
  apply Finmap.ext_lookup
  intro q
  change FMap.get (applyPatch (applyPatch fs first) last) q = FMap.get (applyPatch fs last) q
  cases hl : FMap.get last q with
  | some e =>
    cases e with
    | delete => rw [applyPatch_get_delete hl, applyPatch_get_delete hl]
    | write f => rw [applyPatch_get_write hl, applyPatch_get_write hl]
  | none =>
    rw [applyPatch_get_none hl, applyPatch_get_none hl]
    apply applyPatch_get_none
    cases hf : FMap.get first q with
    | none => rfl
    | some e =>
      have memFirst : q ∈ FMap.dom first := Finmap.mem_keys.mpr (Finmap.mem_iff.mpr ⟨e, hf⟩)
      have memLast := covered memFirst
      obtain ⟨v, hv⟩ := Finmap.mem_iff.mp (Finmap.mem_keys.mp memLast)
      change FMap.get last q = some v at hv
      rw [hl] at hv
      contradiction

/-- Actual earlier live filesystems, not memo witnesses or hypothetical sandbox views. -/
def earlierLiveFilesystems (pre : Prefix m h .live prog start) : List (FS sig) :=
  [start.fs] ++ pre.trace.flatMap (fun d => [d.before.fs, d.selected.fs]) ++
    pre.trace.dropLast.map (fun d => d.after.fs)

def RepairProvenance (pre : Prefix m h .live prog start) (repair : Patch sig) : Prop :=
  ∀ q file, FMap.get repair q = some (.write file) →
    ∃ fs ∈ earlierLiveFilesystems pre, FMap.get fs q = some file

/-- Normalized proof support for same-path witness provenance. -/
def WitnessProvenance (initial : WitnessMap sig) (records : Records sig) (fs : FS sig) : Prop :=
  (∃ key witness, FMap.get initial key = some witness ∧ fs = witness.fs) ∨
    ∀ q file, FMap.get fs q = some file → (q, file) ∈ records

/-- E.6 same-path provenance over whole E.3 maps, not whole-witness occurrence. -/
def RecordedWitnessProvenance (initial : WitnessMap sig) (records : RecordCollection sig)
    (fs : FS sig) : Prop :=
  (∃ key witness, FMap.get initial key = some witness ∧ fs = witness.fs) ∨
    ∀ q file, FMap.get fs q = some file →
      ∃ record ∈ records, FMap.get record q = some (.write file)

/-- Only an exact occurrence bridge permits reuse of normalized provenance proofs. -/
theorem recordedWitnessProvenance_iff_normalized (initial : WitnessMap sig)
    (maps : RecordCollection sig) (files : Records sig)
    (occurrences : ∀ q file, (q, file) ∈ recordOccurrences maps ↔ (q, file) ∈ files) (fs : FS sig) :
    RecordedWitnessProvenance initial maps fs ↔ WitnessProvenance initial files fs := by
  constructor
  · rintro (chosen | copied)
    · exact Or.inl chosen
    · exact Or.inr (fun q file lookup => (occurrences q file).mp (copied q file lookup))
  · rintro (chosen | copied)
    · exact Or.inl chosen
    · exact Or.inr (fun q file lookup => (occurrences q file).mpr (copied q file lookup))

theorem Boundary.recordedWitnessProvenance_iff {pre : Prefix m h .live prog start}
    (b : Boundary pre) (initial : WitnessMap sig) (fs : FS sig) :
    RecordedWitnessProvenance initial b.paperRecords fs ↔ WitnessProvenance initial b.records fs :=
  recordedWitnessProvenance_iff_normalized initial _ _ b.paperRecords_occurrences fs

theorem RecordedWitnessProvenance.mono {initial : WitnessMap sig}
    {old new : RecordCollection sig} {fs : FS sig}
    (provenance : RecordedWitnessProvenance initial old fs) (subset : old ⊆ new) :
    RecordedWitnessProvenance initial new fs := by
  rcases provenance with chosen | copied
  · exact Or.inl chosen
  · right
    intro q file lookup
    obtain ⟨record, member, present⟩ := copied q file lookup
    exact ⟨record, subset member, present⟩

def prefixResult (sb : Sandbox sig) : Result sig :=
  ⟨none, sb.patch, sb.reads, sb.writes, sb.output⟩

/-- The literal next-call equation, with explicit partial-concatenation typing. -/
def EntryFold (p : sig.Probe) (sb : Sandbox sig) (current base : FS sig) (env : Env sig) : Prop :=
  ∀ input result, m.denotes p input current env result →
    ∀ (hin : sb.input.flag = .open) (hout : sb.output.flag = .open),
      m.denotes p (sb.input ++'hin input) base env (combineResults (prefixResult sb) result hout)

/-- At an endpoint, any permitted first selection supplies its environment.
At a selected boundary, use that selection. Neither case needs a future probe. -/
def SelectedAt {pre : Prefix m h .live prog start} (b : Boundary pre)
    (p : sig.Probe) (i : Nat) (env : Env sig) : Prop :=
  match b with
  | .final => ∃ selection world, h.select prog pre.final selection world ∧
      selection.head = .pipeline p i ∧ world.env = env
  | .selected selection world _ => selection.head = .pipeline p i ∧ world.env = env

/-- E.6 progressed entry: exact repair domain, prefix equation, provenance, and fold. -/
structure RepairedEntry (pre : Prefix m h .live prog start) (b : Boundary pre)
    (p : sig.Probe) (sb : Sandbox sig) (env : Env sig) (repair : Patch sig) : Prop where
  domain : FMap.dom repair = FMap.dom sb.patch
  denotation : m.denotes p sb.input (applyPatch b.world.fs repair) env (prefixResult sb)
  provenance : RepairProvenance pre repair
  fold : EntryFold (m := m) p sb b.world.fs (applyPatch b.world.fs repair) env

/-- Entry-level E.6 package, excluding global cache and all-memo obligations. -/
structure EntryPrefix (pre : Prefix m h .live prog start) (b : Boundary pre)
    (entry i : Nat) (p : sig.Probe) (sb : Sandbox sig) : Prop where
  firstEnvironment : openSteps pre.trace (.pipeline entry i) ≠ [] →
    ∃ env, FirstEnvironment pre.trace (.pipeline entry i) env
  progressed : openSteps pre.trace (.pipeline entry i) ≠ [] →
    ∀ env, FirstEnvironment pre.trace (.pipeline entry i) env →
      ∃ repair, RepairedEntry pre b p sb env repair
  zero : openSteps pre.trace (.pipeline entry i) = [] →
    sb = Sandbox.initial sb.base ∧
    ∀ env, SelectedAt b p i env →
      let repair : Patch sig := ∅
      let base := applyPatch b.world.fs repair
      base = b.world.fs ∧ EntryFold (m := m) p sb b.world.fs base env

/-- Global E.6 conclusions remain explicit, outside the entry-level relation package. -/
structure CachePrefixProperties (witnesses : WitnessMap sig)
    (pre : Prefix m h .live prog start) (b : Boundary pre) : Prop where
  cache : WellFormedCache m b.world.cache
  entries : ∀ entry i p sb, b.livePipeline entry i → b.assigned entry i p →
    Cacheable m p → FMap.get b.world.sandbox i = some sb → EntryPrefix pre b entry i p sb
  memos : ∀ key memo, FMap.get b.world.cache key = some memo →
    ∃ fs, EntryWitness m key memo fs ∧ RecordedWitnessProvenance witnesses b.paperRecords fs

set_option linter.unusedVariables false in
/-- Absorption turns a progressed prefix denotation into the printed next-call fold. -/
theorem EntryFold.of_denotation (commands : WellFormedCommands m) (p : sig.Probe)
    (cacheable : Cacheable m p) (sb : Sandbox sig) (current : FS sig) (repair : Patch sig) (env : Env sig)
    (domain : FMap.dom repair = FMap.dom sb.patch)
    (absorbed : applyPatch current sb.patch = current)
    (denotation : m.denotes p sb.input (applyPatch current repair) env (prefixResult sb)) :
    EntryFold (m := m) p sb current (applyPatch current repair) env := by
  intro input result call hin hout
  have baseAbsorption : applyPatch (applyPatch current repair) sb.patch = current := by
    rw [patch_absorption current repair sb.patch (by rw [domain]), absorbed]
  apply commands.chunk p cacheable env (applyPatch current repair) sb.input input (prefixResult sb) result
    hin rfl hout denotation
  simpa only [prefixResult, baseAbsorption] using call

/-- An empty chronological history has the exact initial sandbox fields. -/
theorem HistoryFields.eq_initial {executor : Executor} (sb : Sandbox sig)
    (fields : HistoryFields ([] : Trace m h executor prog) sb) : sb = Sandbox.initial sb.base := by
  rcases fields with ⟨patch, input, output, reads, writes⟩
  change sb.patch = ∅ at patch
  change some Chunk.emptyOpen = some sb.input at input
  change some Chunk.emptyOpen = some sb.output at output
  change sb.reads = ∅ at reads
  change sb.writes = ∅ at writes
  cases sb with
  | mk base inp rd wr delta out =>
    change delta = ∅ at patch
    change rd = ∅ at reads
    change wr = ∅ at writes
    simp only [Option.some.injEq] at input output
    subst inp; subst out; subst rd; subst wr; subst delta
    rfl

set_option linter.unusedVariables false in
/-- With no prior open call, the next-call fold is the call itself. -/
theorem EntryFold.initial (p : sig.Probe) (base current : FS sig) (env : Env sig) :
    EntryFold (m := m) p (Sandbox.initial base) current current env := by
  intro input result call hin hout
  have inputEq : Chunk.concat (Sandbox.initial base).input input hin = input := by cases input; rfl
  have resultEq : combineResults (prefixResult (Sandbox.initial base)) result hout = result := by
    cases result with
    | mk status patch reads writes output =>
      cases output
      simp [Sandbox.initial, prefixResult, combineResults, Chunk.concat, Chunk.emptyOpen,
        FMap.merge_empty_earlier, FMap.filterKeys, FMap.keys]
  rw [inputEq, resultEq]
  exact call

/-- E.6's zero-open entry case needs no empty-input command denotation. -/
theorem EntryPrefix.zero_clause (host : HostWellFormed m h)
    (pre : Prefix m h .live prog start) (operational : Operational pre) (b : Boundary pre)
    (entry i : Nat) (p : sig.Probe) (sb : Sandbox sig) (live : b.livePipeline entry i)
    (present : FMap.get b.world.sandbox i = some sb)
    (empty : openSteps pre.trace (.pipeline entry i) = []) :
    sb = Sandbox.initial sb.base ∧ ∀ env, SelectedAt b p i env →
      let repair : Patch sig := ∅
      let base := applyPatch b.world.fs repair
      base = b.world.fs ∧ EntryFold (m := m) p sb b.world.fs base env := by
  have fields := Operational.liveHistories host pre operational b entry i sb live present
  have openEq := openSteps_eq_componentSteps pre.trace (.pipeline entry i) live.2.2
  rw [← openEq, empty] at fields
  have initial := HistoryFields.eq_initial sb fields
  refine ⟨initial, ?_⟩
  intro env _
  dsimp only
  refine ⟨applyPatch_empty _, ?_⟩
  rw [applyPatch_empty, initial]
  exact EntryFold.initial p sb.base b.world.fs env

set_option linter.unusedVariables false in
/-- Exact dependency-path agreement transports the entire result, including timestamps. -/
theorem DependencyFaithfulness.transport_exact (commands : WellFormedCommands m)
    (p : sig.Probe) (input : Chunk) (fs target : FS sig) (env : Env sig) (result : Result sig)
    (call : m.denotes p input fs env result)
    (same : ∀ q ∈ FMap.dom result.reads ∪ FMap.dom result.writes,
      FMap.get fs q = FMap.get target q) : m.denotes p input target env result := by
  have maps : fs ↾ (FMap.dom result.reads ∪ FMap.dom result.writes) =
      target ↾ (FMap.dom result.reads ∪ FMap.dom result.writes) := FMap.restrict_congr same
  have approx : FSApprox (fs ↾ (FMap.dom result.reads ∪ FMap.dom result.writes))
      (target ↾ (FMap.dom result.reads ∪ FMap.dom result.writes)) := by
    rw [maps]
    exact FSApprox.of_contents (fun _ => rfl)
  obtain ⟨patch, reads, transported, patchApprox, sameDomain, readTimes⟩ :=
    commands.dependencies.transport p input fs env result call target approx
  have valid := commands.dependencies.valid p input fs env result call
  have readsEq : reads = result.reads := by
    apply Finmap.ext_lookup
    intro q
    change FMap.get reads q = FMap.get result.reads q
    cases old : FMap.get result.reads q with
    | none =>
      apply FMap.get_eq_none.mpr
      intro member
      have oldDomain : q ∈ FMap.dom result.reads := by
        rw [← sameDomain]
        exact Finmap.mem_keys.mpr member
      obtain ⟨v, hv⟩ := Finmap.mem_iff.mp (Finmap.mem_keys.mp oldDomain)
      change FMap.get result.reads q = some v at hv
      rw [old] at hv
      contradiction
    | some oldTime =>
      have inReads : q ∈ FMap.dom result.reads := Finmap.mem_keys.mpr (Finmap.mem_iff.mpr ⟨oldTime, old⟩)
      have inNew : q ∈ FMap.dom reads := by rwa [sameDomain]
      obtain ⟨newTime, new⟩ := Finmap.mem_iff.mp (Finmap.mem_keys.mp inNew)
      change FMap.get reads q = some newTime at new
      have inFS : q ∈ FMap.dom fs := valid.1 (Or.inl inReads)
      obtain ⟨file, fileAt⟩ := Finmap.mem_iff.mp (Finmap.mem_keys.mp inFS)
      change FMap.get fs q = some file at fileAt
      have targetAt : FMap.get target q = some file := (same q (Or.inl inReads)).symm.trans fileAt
      obtain ⟨file', fileAt', newEq⟩ := readTimes q newTime new
      rw [targetAt] at fileAt'
      cases Option.some.inj fileAt'
      have oldEq := valid.2.1 q oldTime file old fileAt
      rw [new]
      congr 1
      exact newEq.symm.trans oldEq
  subst reads
  have result' := commands.timestamps.retimestamp p input target env {result with patch := patch} transported result.patch
    ⟨patchApprox.1.symm, fun q mem => by
      have mem' : q ∈ FMap.dom patch := by rw [patchApprox.1]; exact mem
      exact (patchApprox.2 q mem').symm⟩
  simpa using result'

/-- A foreign ordered step preserves a progressed entry's exact prefix denotation. -/
theorem EntryPrefix.foreign_denotation (commands : WellFormedCommands m) (host : HostWellFormed m h)
    (pre post : Prefix m h .live prog start) (preOperational : Operational pre)
    (postOperational : Operational post) (postOrdered : ExitOrdered post.trace)
    (b : Boundary pre) (entry slot : Nat) (p : sig.Probe) (sb : Sandbox sig)
    (live : b.livePipeline entry slot) (present : FMap.get b.world.sandbox slot = some sb)
    (d : StepDerivation m h .live prog) (before : d.before = pre.final)
    (boundary : match b with
      | .final => True
      | .selected selection world _ => d.selection = selection ∧ d.selected = world)
    (joined : post.trace = pre.trace ++ [d])
    (foreign : componentAt post.trace pre.trace.length d ≠ some (.pipeline entry slot))
    (env : Env sig) (repair : Patch sig)
    (oldCall : m.denotes p sb.input (applyPatch b.world.fs repair) env (prefixResult sb)) :
    m.denotes p sb.input (applyPatch d.after.fs repair) env (prefixResult sb) := by
  apply DependencyFaithfulness.transport_exact commands p sb.input (applyPatch b.world.fs repair)
    (applyPatch d.after.fs repair) env (prefixResult sb) oldCall
  intro q depends
  have inEntry : q ∈ FMap.dom sb.patch ∪ FMap.dom sb.reads ∪ FMap.dom sb.writes := by
    rcases depends with read | write
    · exact Or.inl (Or.inr read)
    · exact Or.inr write
  have stable := Operational.live_foreign_extension host pre post preOperational postOperational postOrdered
    b entry slot sb live present d before boundary joined foreign q inEntry
  cases lookup : FMap.get repair q with
  | none => rw [applyPatch_get_none lookup, applyPatch_get_none lookup, stable]
  | some edit =>
    cases edit with
    | delete => rw [applyPatch_get_delete lookup, applyPatch_get_delete lookup]
    | write file => rw [applyPatch_get_write lookup, applyPatch_get_write lookup]

/-- The finite preimage patch retains exactly its stated finite domain. -/
theorem prePatch_domain (fs : FS sig) (paths : Finset sig.Path) :
    FMap.dom (prePatch fs paths) = (↑paths : Set sig.Path) := by
  ext q
  change q ∈ (paths.toList.map fun q => (⟨q, match FMap.get fs q with
    | some file => Edit.write file
    | none => .delete⟩ : Sigma (fun _ : sig.Path => Edit sig))).toFinmap ↔ q ∈ paths
  rw [Finmap.mem_list_toFinmap]
  constructor
  · rintro ⟨value, member⟩
    obtain ⟨r, inPaths, equal⟩ := List.mem_map.mp member
    have same : r = q := congrArg Sigma.fst equal
    simpa [same] using inPaths
  · intro member
    refine ⟨_, List.mem_map.mpr ⟨q, ?_, rfl⟩⟩
    simpa using member

/-- Lookup distinguishes an absent patch entry from an explicit deletion marker. -/
theorem prePatch_lookup (fs : FS sig) (paths : Finset sig.Path) (q : sig.Path) :
    FMap.get (prePatch fs paths) q =
      if q ∈ paths then some ((FMap.get fs q).map Edit.write |>.getD .delete) else none := by
  by_cases member : q ∈ paths
  · have inDomain : q ∈ FMap.dom (prePatch fs paths) := by simpa [prePatch_domain] using member
    change q ∈ prePatch fs paths at inDomain
    obtain ⟨value, found⟩ := Finmap.mem_iff.mp inDomain
    change FMap.get (prePatch fs paths) q = some value at found
    have inList := List.of_mem_dlookup (by simpa [FMap.get, prePatch, Finmap.dlookup_list_toFinmap] using found)
    obtain ⟨r, _, equal⟩ := List.mem_map.mp inList
    have same : r = q := congrArg Sigma.fst equal
    subst r
    cases equal
    cases lookup : Finmap.lookup q fs <;> simpa [member, FMap.get, lookup] using found
  · simp only [member, ite_false]
    apply FMap.get_eq_none.mpr
    intro inMap
    have inDomain : q ∈ FMap.dom (prePatch fs paths) := Finmap.mem_keys.mpr inMap
    rw [prePatch_domain] at inDomain
    exact member inDomain

/-- A progressed history has a real first environment, with no default. -/
theorem firstEnvironment_exists (trace : Trace m h .live prog) (k : Component)
    (progressed : openSteps trace k ≠ []) : ∃ env, FirstEnvironment trace k env := by
  cases hs : componentSteps trace k with
  | nil => simp [openSteps, hs] at progressed
  | cons first rest => exact ⟨first.selected.env, first, by simp [hs], rfl⟩

/-- Result typing discharges the two partial-fold typing guards. -/
theorem prefixResult_flags (shape : DenotationShape m) (p : sig.Probe) (sb : Sandbox sig)
    (fs : FS sig) (env : Env sig) (denotation : m.denotes p sb.input fs env (prefixResult sb)) :
    sb.input.flag = .open ∧ sb.output.flag = .open := by
  have typed := shape p sb.input fs env _ denotation
  cases flag : sb.input.flag with
  | «open» => exact ⟨rfl, (typed.1 flag).1⟩
  | eof =>
    obtain ⟨_, es, impossible⟩ := typed.2 flag
    contradiction

/-- The repair-update identity used for a new live open patch, including deletions. -/
theorem repair_update (fs : FS sig) (repair accumulated next : Patch sig)
    (domain : FMap.dom repair = FMap.dom accumulated) :
    let updated := repair ⊎ prePatch fs (FMap.keys next \ FMap.keys accumulated)
    FMap.dom updated = FMap.dom (accumulated ⊎ next) ∧
      applyPatch (applyPatch fs next) updated = applyPatch fs repair := by
  dsimp only
  constructor
  · rw [FMap.dom_merge_union, FMap.dom_merge_union, prePatch_domain, domain]
    ext q
    simp only [Set.mem_union, FMap.dom, FMap.keys, Finmap.mem_keys]
    by_cases h : q ∈ accumulated <;> simp [h, Finmap.mem_keys]
  · apply Finmap.ext_lookup
    intro q
    change FMap.get (applyPatch (applyPatch fs next)
      (repair ⊎ prePatch fs (FMap.keys next \ FMap.keys accumulated))) q =
      FMap.get (applyPatch fs repair) q
    cases hr : FMap.get repair q with
    | some edit =>
      have inRepair : q ∈ FMap.dom repair := Finmap.mem_keys.mpr (Finmap.mem_iff.mpr ⟨edit, hr⟩)
      have inAccumulated : q ∈ FMap.keys accumulated := by
        have := domain ▸ inRepair
        exact this
      have noneNew : FMap.get (prePatch fs (FMap.keys next \ FMap.keys accumulated)) q = none := by
        simp [prePatch_lookup, inAccumulated]
      have merged := FMap.get_merge_of_not_mem repair (prePatch fs (FMap.keys next \ FMap.keys accumulated)) q noneNew
      cases edit with
      | delete => rw [applyPatch_get_delete (merged.trans hr), applyPatch_get_delete hr]
      | write file => rw [applyPatch_get_write (merged.trans hr), applyPatch_get_write hr]
    | none =>
      have notRepair : q ∉ FMap.dom repair := by
        intro present
        obtain ⟨v, hv⟩ := Finmap.mem_iff.mp (Finmap.mem_keys.mp present)
        change FMap.get repair q = some v at hv
        rw [hr] at hv
        contradiction
      have notAccumulated : q ∉ FMap.keys accumulated := by
        intro present
        apply notRepair
        rw [domain]
        exact present
      rw [applyPatch_get_none hr]
      cases hn : FMap.get next q with
      | none =>
        have notNext : q ∉ FMap.keys next := by
          intro present
          obtain ⟨v, hv⟩ := Finmap.mem_iff.mp (Finmap.mem_keys.mp present)
          change FMap.get next q = some v at hv
          rw [hn] at hv
          contradiction
        have noneNew : FMap.get (prePatch fs (FMap.keys next \ FMap.keys accumulated)) q = none := by
          simp [prePatch_lookup, notNext]
        have merged := FMap.get_merge_of_not_mem repair (prePatch fs (FMap.keys next \ FMap.keys accumulated)) q noneNew
        rw [applyPatch_get_none (merged.trans hr), applyPatch_get_none hn]
      | some edit =>
        have inNext : q ∈ FMap.keys next := Finmap.mem_keys.mpr (Finmap.mem_iff.mpr ⟨edit, hn⟩)
        cases hf : FMap.get fs q with
        | none =>
          have restored : FMap.get (prePatch fs (FMap.keys next \ FMap.keys accumulated)) q = some .delete := by
            simp [prePatch_lookup, inNext, notAccumulated, hf]
          have merged := FMap.get_merge_of_mem repair _ q .delete restored
          rw [applyPatch_get_delete merged]
        | some file =>
          have restored : FMap.get (prePatch fs (FMap.keys next \ FMap.keys accumulated)) q = some (.write file) := by
            simp [prePatch_lookup, inNext, notAccumulated, hf]
          have merged := FMap.get_merge_of_mem repair _ q (.write file) restored
          rw [applyPatch_get_write merged]

end
end IncrPP
end Incr

/-!
# Cache witness bookkeeping for E.6

These lemmas preserve existing fixed initial witnesses and actual record
provenance through the paper's store, retain, and erase choices.
-/

namespace Incr.IncrPP

noncomputable section

variable {sig : Signature} {m : CommandModel sig}

/-- Extending the actual record collection preserves same-path witness provenance. -/
theorem WitnessProvenance.mono {initial : WitnessMap sig} {old new : Records sig} {fs : FS sig}
    (provenance : WitnessProvenance initial old fs) (records : ∀ item ∈ old, item ∈ new) :
    WitnessProvenance initial new fs := by
  rcases provenance with fixed | recorded
  · exact Or.inl fixed
  · exact Or.inr (fun q file lookup => records _ (recorded q file lookup))

/-- A concrete entry witness is exactly enough for the printed cache certificate. -/
theorem EntryWitness.cache_certificate {key : Key sig} {memo : Memo sig} {fs : FS sig}
    (witness : EntryWitness m key memo fs) :
    ∃ p env input fs', Cacheable m p ∧ input.flag = .eof ∧
      key = cacheKey m p env input ∧ m.denotes p input fs' env memo.result := by
  obtain ⟨p, env, input, cacheable, eof, keyEq, call⟩ := witness
  exact ⟨p, env, input, fs, cacheable, eof, keyEq, call⟩

/-- E.6's per-memo witness package, used only as a proof invariant. -/
def CacheWitnessed (initial : WitnessMap sig) (records : Records sig) (cache : Cache sig) : Prop :=
  ∀ key memo, FMap.get cache key = some memo →
    ∃ fs, EntryWitness m key memo fs ∧ WitnessProvenance initial records fs

/-- Per-entry witnesses imply the complete printed well-formed-cache clause. -/
theorem CacheWitnessed.wellFormed {initial : WitnessMap sig} {records : Records sig} {cache : Cache sig}
    (witnessed : CacheWitnessed (m := m) initial records cache) : WellFormedCache m cache := by
  intro key memo lookup
  obtain ⟨fs, witness, _⟩ := witnessed key memo lookup
  exact EntryWitness.cache_certificate witness

/-- Fixed initial choices give one valid witness for every initial memo. -/
theorem CacheWitnessed.initial {initial : WitnessMap sig} {records : Records sig} {cache : Cache sig}
    (chosen : WitnessesFor m cache initial) : CacheWitnessed (m := m) initial records cache := by
  intro key memo lookup
  obtain ⟨witness, witnessAt, p, env, cacheable, eof, keyEq, call⟩ := chosen.2 key memo lookup
  exact ⟨witness.fs, ⟨p, env, witness.input, cacheable, eof, keyEq, call⟩,
    Or.inl ⟨key, witness, witnessAt, rfl⟩⟩

/-- A cache policy preserves all remaining witnesses and uses the supplied witness if it stores. -/
theorem CacheWitnessed.update {initial : WitnessMap sig} {oldRecords newRecords : Records sig}
    {cache next : Cache sig} {key : Key sig} {memo : Memo sig}
    (witnessed : CacheWitnessed (m := m) initial oldRecords cache)
    (moreRecords : ∀ item ∈ oldRecords, item ∈ newRecords)
    (update : CacheUpdate cache key memo next)
    (stored : ∃ fs, EntryWitness m key memo fs ∧ WitnessProvenance initial newRecords fs) :
    CacheWitnessed (m := m) initial newRecords next := by
  intro lookupKey lookupMemo lookup
  rcases update with store | keep | erase
  · subst next
    by_cases same : lookupKey = key
    · subst lookupKey
      rw [FMap.get_set_self] at lookup
      cases Option.some.inj lookup
      exact stored
    · have original : FMap.get cache lookupKey = some lookupMemo := by
        rwa [FMap.get_set_other same] at lookup
      obtain ⟨fs, witness, provenance⟩ := witnessed lookupKey lookupMemo original
      exact ⟨fs, witness, provenance.mono moreRecords⟩
  · subst next
    obtain ⟨fs, witness, provenance⟩ := witnessed lookupKey lookupMemo lookup
    exact ⟨fs, witness, provenance.mono moreRecords⟩
  · subst next
    have different : lookupKey ≠ key := lookup_erase_ne lookup
    have original : FMap.get cache lookupKey = some lookupMemo := by
      rwa [FMap.get_erase_of_ne different] at lookup
    obtain ⟨fs, witness, provenance⟩ := witnessed lookupKey lookupMemo original
    exact ⟨fs, witness, provenance.mono moreRecords⟩

/-- Retaining or erasing entries cannot invent a memo witness. -/
theorem CacheWitnessed.subcache {initial : WitnessMap sig} {oldRecords newRecords : Records sig}
    {cache next : Cache sig} (witnessed : CacheWitnessed (m := m) initial oldRecords cache)
    (moreRecords : ∀ item ∈ oldRecords, item ∈ newRecords)
    (contained : ∀ key memo, FMap.get next key = some memo → FMap.get cache key = some memo) :
    CacheWitnessed (m := m) initial newRecords next := by
  intro key memo found
  obtain ⟨fs, witness, provenance⟩ := witnessed key memo (contained key memo found)
  exact ⟨fs, witness, provenance.mono moreRecords⟩

variable {h : Host sig} {executor : Executor} {prog : sig.Prog} {start : World sig}

/-- Actual final-world records are retained by every connected prefix, including the empty prefix. -/
theorem Prefix.final_world_records (pre : Prefix m h executor prog start) (record : sig.Path × File sig)
    (member : record ∈ worldRecords pre.final) : record ∈ pre.records := by
  have collect {a b : World sig} {trace : Trace m h executor prog}
      (connected : Connected a trace b) (recorded : record ∈ worldRecords b) :
      record ∈ worldRecords a ++ trace.flatMap StepDerivation.records := by
    induction connected with
    | nil => exact List.mem_append_left _ recorded
    | cons d rest final tail ih =>
      rcases List.mem_append.mp (ih recorded) with after | later
      · apply List.mem_append_right
        apply List.mem_flatMap.mpr
        refine ⟨d, by simp, ?_⟩
        simp only [StepDerivation.records, List.mem_append]
        tauto
      · exact List.mem_append_right _ (by simpa only [List.flatMap_cons, List.mem_append] using Or.inr later)
  exact collect pre.connected member

/-- Every actual boundary filesystem record is retained in that boundary's record collection. -/
theorem Boundary.fs_record (pre : Prefix m h executor prog start) (b : Boundary pre)
    (q : sig.Path) (file : File sig) (lookup : FMap.get b.world.fs q = some file) :
    (q, file) ∈ b.records := by
  cases b with
  | final =>
    apply pre.final_world_records
    simp only [Boundary.world] at lookup
    simp only [worldRecords, List.mem_append]
    exact Or.inl (Or.inl (mem_fsRecords_of_get lookup))
  | selected selection world allowed =>
    simp only [Boundary.world] at lookup
    simp only [Boundary.records, worldRecords, List.mem_append]
    have record := mem_fsRecords_of_get lookup
    tauto

/-- Every world retained by an actual recorded step contributes its records to the prefix. -/
theorem Prefix.step_world_record (pre : Prefix m h executor prog start)
    (d : StepDerivation m h executor prog) (member : d ∈ pre.trace)
    (record : sig.Path × File sig)
    (world : record ∈ worldRecords d.before ∨ record ∈ worldRecords d.selected ∨
      record ∈ worldRecords d.after) : record ∈ pre.records := by
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨d, member, ?_⟩
  simp only [StepDerivation.records, List.mem_append]
  tauto

/-- Every file copied from an earlier live filesystem occurs in the actual prefix records. -/
theorem Prefix.earlier_fs_record (pre : Prefix m h .live prog start)
    (fs : FS sig) (earlier : fs ∈ earlierLiveFilesystems pre)
    (q : sig.Path) (file : File sig) (lookup : FMap.get fs q = some file) :
    (q, file) ∈ pre.records := by
  simp only [earlierLiveFilesystems, List.mem_append,
    List.mem_flatMap, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at earlier
  rcases earlier with (startEq | ⟨d, member, beforeEq | selectedEq⟩) | ⟨d, member, afterEq⟩
  · subst fs
    apply List.mem_append_left
    simp only [worldRecords, List.mem_append]
    exact Or.inl (Or.inl (mem_fsRecords_of_get lookup))
  · subst fs
    apply pre.step_world_record d member
    left
    simp only [worldRecords, List.mem_append]
    exact Or.inl (Or.inl (mem_fsRecords_of_get lookup))
  · subst fs
    apply pre.step_world_record d member
    right; left
    simp only [worldRecords, List.mem_append]
    exact Or.inl (Or.inl (mem_fsRecords_of_get lookup))
  · subst fs
    apply pre.step_world_record d (List.dropLast_subset pre.trace member)
    right; right
    simp only [worldRecords, List.mem_append]
    exact Or.inl (Or.inl (mem_fsRecords_of_get lookup))

/-- A repaired base copies every file from the current boundary or an earlier live filesystem. -/
theorem RepairProvenance.base_recorded {initial : WitnessMap sig}
    (pre : Prefix m h .live prog start) (b : Boundary pre) (repair : Patch sig)
    (provenance : RepairProvenance pre repair) :
    WitnessProvenance initial b.records (applyPatch b.world.fs repair) := by
  right
  intro q file lookup
  cases repairAt : FMap.get repair q with
  | none =>
    rw [applyPatch_get_none repairAt] at lookup
    exact b.fs_record pre q file lookup
  | some edit =>
    cases edit with
    | delete =>
      rw [applyPatch_get_delete repairAt] at lookup
      contradiction
    | write written =>
      rw [applyPatch_get_write repairAt] at lookup
      cases Option.some.inj lookup
      obtain ⟨fs, earlier, present⟩ := provenance q file repairAt
      have record := pre.earlier_fs_record fs earlier q file present
      cases b with
      | final => exact record
      | selected selection world allowed => exact List.mem_append_left _ record

/-- A completed call and recorded filesystem give the exact witness for a new memo. -/
theorem CacheWitnessed.call_certificate (initial : WitnessMap sig) (records : Records sig)
    (p : sig.Probe) (input : Chunk) (fs : FS sig) (env : Env sig) (memo : Memo sig)
    (cacheable : Cacheable m p) (eof : input.flag = .eof)
    (call : m.denotes p input fs env memo.result)
    (recorded : ∀ q file, FMap.get fs q = some file → (q, file) ∈ records) :
    ∃ witness, EntryWitness m (cacheKey m p env input) memo witness ∧
      WitnessProvenance initial records witness := by
  exact ⟨fs, ⟨p, env, input, cacheable, eof, rfl, call⟩, Or.inr recorded⟩

/-- An actual next step records the entire prior endpoint or selected boundary. -/
theorem Boundary.records_snoc (pre post : Prefix m h executor prog start)
    (b : Boundary pre) (d : StepDerivation m h executor prog)
    (joined : post.trace = pre.trace ++ [d])
    (selected : match b with
      | .final => True
      | .selected _ world _ => d.selected = world) :
    ∀ record ∈ b.records, record ∈ post.records := by
  intro record member
  have old : ∀ record ∈ pre.records, record ∈ post.records := by
    intro item present
    simp only [Prefix.records, joined, List.flatMap_append, List.mem_append, List.flatMap_cons,
      List.flatMap_nil] at present ⊢
    tauto
  cases b with
  | final => exact old record member
  | selected selection world allowed =>
    simp only [Boundary.records, List.mem_append] at member
    rcases member with prior | chosen
    · exact old record prior
    · have selectedWorld : record ∈ worldRecords d.selected := by rwa [selected]
      apply post.step_world_record d
      · rw [joined]
        exact List.mem_append_right _ (by simp)
      · exact Or.inr (Or.inl selectedWorld)

/-- Earlier actual live filesystems remain earlier after an actual next step. -/
theorem earlierLiveFilesystems_snoc (pre post : Prefix m h .live prog start)
    (d : StepDerivation m h .live prog) (joined : post.trace = pre.trace ++ [d]) :
    ∀ fs ∈ earlierLiveFilesystems pre, fs ∈ earlierLiveFilesystems post := by
  intro fs earlier
  simp only [earlierLiveFilesystems, joined, List.flatMap_append, List.dropLast_concat,
    List.mem_append, List.mem_flatMap, List.mem_map] at earlier ⊢
  rcases earlier with (initial | ⟨step, member, fromStep⟩) | ⟨step, member, after⟩
  · tauto
  · exact Or.inl (Or.inr (Or.inl ⟨step, member, fromStep⟩))
  · have oldStep := List.dropLast_subset pre.trace member
    exact Or.inr ⟨step, oldStep, after⟩

/-- The selected filesystem of an actual new step is earlier than its resulting endpoint. -/
theorem selected_fs_earlier (pre post : Prefix m h .live prog start)
    (d : StepDerivation m h .live prog) (joined : post.trace = pre.trace ++ [d]) :
    d.selected.fs ∈ earlierLiveFilesystems post := by
  unfold earlierLiveFilesystems
  apply List.mem_append_left
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨d, ?_, ?_⟩
  · rw [joined]
    exact List.mem_append_right _ (by simp)
  · simp

/-- Repair updates retain prior provenance and copy new records from the actual selected filesystem. -/
theorem RepairProvenance.update (pre post : Prefix m h .live prog start)
    (d : StepDerivation m h .live prog) (joined : post.trace = pre.trace ++ [d])
    (repair accumulated next : Patch sig) (provenance : RepairProvenance pre repair) :
    RepairProvenance post
      (repair ⊎ prePatch d.selected.fs (FMap.keys next \ FMap.keys accumulated)) := by
  intro q file lookup
  rw [FMap.get_merge_elim] at lookup
  cases new : FMap.get (prePatch d.selected.fs (FMap.keys next \ FMap.keys accumulated)) q with
  | none =>
    rw [new] at lookup
    obtain ⟨fs, earlier, found⟩ := provenance q file lookup
    exact ⟨fs, earlierLiveFilesystems_snoc pre post d joined fs earlier, found⟩
  | some edit =>
    rw [new] at lookup
    simp only [Option.elim_some, Option.some.injEq] at lookup
    subst edit
    have formula := prePatch_lookup d.selected.fs (FMap.keys next \ FMap.keys accumulated) q
    rw [new] at formula
    split at formula
    next member =>
      cases fsAt : FMap.get d.selected.fs q with
      | none => simp [fsAt] at formula
      | some actual =>
        simp only [fsAt, Option.map_some, Option.getD_some, Option.some.injEq, Edit.write.injEq] at formula
        cases formula
        exact ⟨d.selected.fs, selected_fs_earlier pre post d joined, fsAt⟩
    next notMember => simp at formula

set_option linter.unusedVariables false in
/-- An open result's accumulator equals the printed combined prefix result. -/
theorem prefixResult_accumulate (sb : Sandbox sig) (input : Chunk) (result : Result sig)
    (hin : sb.input.flag = .open) (hout : sb.output.flag = .open)
    (statusEq : result.status = none) :
    prefixResult (sb.accumulate input result hin hout) =
      combineResults (prefixResult sb) result hout := by
  cases result with
  | mk status patch reads writes output =>
    have status' : status = none := statusEq
    subst status
    rfl

/-- A live open step extends the repaired prefix denotation and preserves its actual provenance. -/
theorem RepairedEntry.advance_open (commands : WellFormedCommands m)
    (pre post : Prefix m h .live prog start) (d : StepDerivation m h .live prog)
    (joined : post.trace = pre.trace ++ [d]) (after : post.final = d.after)
    (p : sig.Probe) (cacheable : Cacheable m p) (sb : Sandbox sig)
    (input : Chunk) (result : Result sig) (hin : sb.input.flag = .open) (hout : sb.output.flag = .open)
    (status : result.status = none) (call : m.denotes p input d.selected.fs d.selected.env result)
    (fsEffect : d.after.fs = applyPatch d.selected.fs result.patch)
    (repair : Patch sig) (domain : FMap.dom repair = FMap.dom sb.patch)
    (provenance : RepairProvenance pre repair)
    (fold : EntryFold (m := m) p sb d.selected.fs (applyPatch d.selected.fs repair) d.selected.env)
    (absorbed : applyPatch post.final.fs (sb.accumulate input result hin hout).patch = post.final.fs) :
    ∃ newRepair, RepairedEntry post .final p (sb.accumulate input result hin hout) d.selected.env newRepair := by
  let newRepair := repair ⊎ prePatch d.selected.fs (FMap.keys result.patch \ FMap.keys sb.patch)
  have update := repair_update d.selected.fs repair sb.patch result.patch domain
  have newDomain : FMap.dom newRepair = FMap.dom (sb.accumulate input result hin hout).patch := by
    exact update.1
  have newBase : applyPatch post.final.fs newRepair = applyPatch d.selected.fs repair := by
    rw [after, fsEffect]
    exact update.2
  have denotation : m.denotes p (sb.accumulate input result hin hout).input
      (applyPatch post.final.fs newRepair) d.selected.env (prefixResult (sb.accumulate input result hin hout)) := by
    rw [newBase, prefixResult_accumulate sb input result hin hout status]
    exact fold input result call hin hout
  refine ⟨newRepair, newDomain, denotation, ?_, ?_⟩
  · exact provenance.update pre post d joined repair sb.patch result.patch
  · exact EntryFold.of_denotation commands p cacheable _ post.final.fs newRepair d.selected.env
      newDomain absorbed denotation

set_option linter.unusedVariables false in
/-- A cacheable close stores exactly the accumulated result of its prefix and final call. -/
theorem accumulatedMemo_result (sb : Sandbox sig) (input : Chunk) (result : Result sig) (es : Nat)
    (hin : sb.input.flag = .open) (hout : sb.output.flag = .open)
    (flag : result.output.flag = .eof) (statusEq : result.status = some es) :
    (accumulatedMemo sb input result es hin hout flag).result =
      combineResults (prefixResult sb) result hout := by
  cases result with
  | mk status patch reads writes output =>
    have status' : status = some es := statusEq
    subst status
    rfl

/-- The complete folded call supplies a new memo witness at the actual repaired base. -/
theorem CacheWitnessed.accumulated_certificate (initial : WitnessMap sig)
    (pre : Prefix m h .live prog start) (b : Boundary pre)
    (p : sig.Probe) (sb : Sandbox sig) (input : Chunk) (result : Result sig) (es : Nat)
    (hin : sb.input.flag = .open) (hout : sb.output.flag = .open)
    (flag : result.output.flag = .eof) (status : result.status = some es)
    (eof : input.flag = .eof) (cacheable : Cacheable m p) (env : Env sig) (repair : Patch sig)
    (provenance : RepairProvenance pre repair)
    (fold : EntryFold (m := m) p sb b.world.fs (applyPatch b.world.fs repair) env)
    (call : m.denotes p input b.world.fs env result) :
    ∃ fs, EntryWitness m (cacheKey m p env (Chunk.concat sb.input input hin))
        (accumulatedMemo sb input result es hin hout flag) fs ∧
      WitnessProvenance initial b.records fs := by
  refine ⟨applyPatch b.world.fs repair, ?_, provenance.base_recorded pre b repair⟩
  refine ⟨p, env, Chunk.concat sb.input input hin, cacheable, ?_, rfl, ?_⟩
  · simpa [Chunk.concat] using eof
  · rw [accumulatedMemo_result sb input result es hin hout flag status]
    exact fold input result call hin hout

/-- E.6's endpoint package survives every permitted host selection. -/
theorem CachePrefixProperties.selected (host : HostWellFormed m h)
    (pre : Prefix m h .live prog start) (operational : Operational pre) (witnesses : WitnessMap sig)
    (properties : CachePrefixProperties witnesses pre .final)
    (selection : Selection sig) (world : World sig) (allowed : h.select prog pre.final selection world) :
    CachePrefixProperties witnesses pre (.selected selection world allowed) := by
  have discipline := host.selectionDiscipline .live prog start pre operational selection world allowed
  have fsEq := discipline.1
  have cacheEq := discipline.2.2.1
  constructor
  · simpa [Boundary.world, cacheEq] using properties.cache
  · intro entry slot p sb live assigned cacheable present
    refine ⟨?_, ?_, ?_⟩
    · intro progressed
      exact firstEnvironment_exists pre.trace (.pipeline entry slot) progressed
    · intro progressed env firstEnv
      cases initializes : selection.init with
      | none =>
        have oldLive : (Boundary.final : Boundary pre).livePipeline entry slot := by
          simpa [Boundary.livePipeline, Boundary.currentEntry, Boundary.componentDomain,
            Boundary.selection?, initializes] using live
        have oldAssigned : (Boundary.final : Boundary pre).assigned entry slot p := by
          simpa only [Boundary.assigned, Boundary.entry_selected_none pre selection world allowed initializes]
            using assigned
        have oldPresent : FMap.get pre.final.sandbox slot = some sb := by
          have allocated := discipline.2.2.2.1
          simp only [initializes] at allocated
          simpa only [Boundary.world, allocated.1] using present
        obtain ⟨repair, repaired⟩ :=
          (properties.entries entry slot p sb oldLive oldAssigned cacheable oldPresent).progressed progressed env firstEnv
        refine ⟨repair, repaired.domain, ?_, repaired.provenance, ?_⟩
        · simpa only [Boundary.world, fsEq] using repaired.denotation
        · simpa only [Boundary.world, fsEq] using repaired.fold
      | some init =>
        have index : pre.trace.length = entry := by
          simpa [Boundary.currentEntry, Boundary.selection?, initializes] using live.1
        subst entry
        have fresh := componentSteps_fresh pre.trace pre.trace.length slot (Nat.le_refl _)
        have empty : openSteps pre.trace (.pipeline pre.trace.length slot) = [] := by simp [openSteps, fresh]
        exact False.elim (progressed empty)
    · intro empty
      exact EntryPrefix.zero_clause host pre operational (.selected selection world allowed)
        entry slot p sb live present empty
  · intro key memo found
    have oldFound : FMap.get pre.final.cache key = some memo := by
      simpa only [Boundary.world, cacheEq] using found
    obtain ⟨fs, witness, provenance⟩ := properties.memos key memo oldFound
    refine ⟨fs, witness, provenance.mono ?_⟩
    intro record member
    exact Or.inl member

/-- Once a component has progressed, appending a step cannot change its first environment. -/
theorem FirstEnvironment.of_snoc {pre post : Prefix m h .live prog start}
    (d : StepDerivation m h .live prog) (joined : post.trace = pre.trace ++ [d])
    (k : Component) (progressed : openSteps pre.trace k ≠ []) (env : Env sig)
    (first : FirstEnvironment post.trace k env) : FirstEnvironment pre.trace k env := by
  have nonempty : componentSteps pre.trace k ≠ [] := by
    intro empty
    apply progressed
    simp [openSteps, empty]
  obtain ⟨firstStep, firstAt, envEq⟩ := first
  rw [joined, componentSteps_snoc] at firstAt
  cases steps : componentSteps pre.trace k with
  | nil => exact False.elim (nonempty steps)
  | cons head tail =>
    simp only [steps, List.cons_append, List.head?_cons, Option.some.injEq] at firstAt
    cases firstAt
    exact ⟨firstStep, by simp [steps], envEq⟩

/-- The host fixes the environment of every actual step to its component's first environment. -/
theorem FirstEnvironment.step_env (host : HostWellFormed m h)
    (pre : Prefix m h .live prog start) (operational : Operational pre)
    (k : Component) (env : Env sig) (first : FirstEnvironment pre.trace k env)
    (pos : Nat) (d : StepDerivation m h .live prog) (atPos : (pre.trace)[pos]? = some d)
    (component : componentAt pre.trace pos d = some k) : d.selected.env = env := by
  obtain ⟨firstStep, firstAt, envEq⟩ := first
  have member : d ∈ componentSteps pre.trace k :=
    (mem_componentSteps_iff pre.trace k d).mpr ⟨pos, atPos, component⟩
  exact ((host.componentEnvironments .live prog start pre operational) k firstStep firstAt d member).2.trans envEq

/-- The selected current entry's assignment is the host's ordered probe assignment. -/
theorem Boundary.assignedProbes_current (pre : Prefix m h .live prog start)
    (selection : Selection sig) (world : World sig) (allowed : h.select prog pre.final selection world)
    (entry slot : Nat) (p : sig.Probe)
    (current : (Boundary.selected selection world allowed).currentEntry = some entry)
    (assigned : (Boundary.selected selection world allowed).assigned entry slot p) :
    ∃ probes, assignedProbes pre.trace selection = some probes ∧ probes[slot]? = some p := by
  obtain ⟨fs, init, entryAt, probeAt⟩ := assigned
  cases initializes : selection.init with
  | some fresh =>
    have index : pre.trace.length = entry := by
      simpa [Boundary.currentEntry, Boundary.selection?, initializes] using current
    subst entry
    have entryEq : some (pre.final.fs, fresh) = some (fs, init) := by
      simpa [Boundary.entry, Boundary.selection?, initializes] using entryAt
    have initEq : fresh = init := congrArg Prod.snd (Option.some.inj entryEq)
    subst init
    exact ⟨fresh.probes, by simp [assignedProbes, initializes], probeAt⟩
  | none =>
    have epoch : (latestPipeline pre.trace).map Prod.fst = some entry := by
      simpa [Boundary.currentEntry, Boundary.selection?, initializes] using current
    obtain ⟨pair, latest, index⟩ := Option.map_eq_some_iff.mp epoch
    rcases pair with ⟨origin, actual⟩
    dsimp at index
    subst entry
    obtain ⟨step, atStep, actualInit⟩ := latestPipeline_origin pre.trace latest
    have bound := latestPipeline_entry_lt pre.trace latest
    have entryEq : some (step.before.fs, actual) = some (fs, init) := by
      simpa [Boundary.entry, Boundary.selection?, initializes, Nat.ne_of_lt bound, atStep, actualInit] using entryAt
    have initEq : actual = init := congrArg Prod.snd (Option.some.inj entryEq)
    subst init
    exact ⟨actual.probes, by simp [assignedProbes, initializes, latest], probeAt⟩

/-- An actual selected pipeline head is its slot's initialized probe. -/
theorem Boundary.selected_head_assigned (host : HostWellFormed m h)
    (pre : Prefix m h .live prog start) (operational : Operational pre)
    (selection : Selection sig) (world : World sig) (allowed : h.select prog pre.final selection world)
    (entry slot : Nat) (p selectedProbe : sig.Probe)
    (current : (Boundary.selected selection world allowed).currentEntry = some entry)
    (assigned : (Boundary.selected selection world allowed).assigned entry slot p)
    (head : selection.head = .pipeline selectedProbe slot) : p = selectedProbe := by
  obtain ⟨probes, assignment, probeAt⟩ :=
    Boundary.assignedProbes_current pre selection world allowed entry slot p current assigned
  have discipline := host.selectionDiscipline .live prog start pre operational selection world allowed
  have law := discipline.2.2.2.2
  rw [head] at law
  obtain ⟨other, otherAssignment, otherProbe⟩ := law.2.2.2
  rw [assignment] at otherAssignment
  cases Option.some.inj otherAssignment
  rw [probeAt] at otherProbe
  exact Option.some.inj otherProbe

/-- A live open judgment is the actual denotation of its selected pipeline probe. -/
theorem LiveDerivation.open_call {before after : World sig} {head : Head sig}
    {returned : Option Chunk} (d : LiveDerivation m before head after returned)
    {p : sig.Probe} {slot : Nat} (pipeline : head = .pipeline p slot)
    (openInput : (LiveDerivation.input d).flag = .open) :
    m.denotes p (LiveDerivation.input d) before.fs before.env (LiveDerivation.result d) ∧
      (LiveDerivation.result d).status = none := by
  subst head
  cases d <;> simp_all [LiveDerivation.input, LiveDerivation.result]

/-- Retaining a repair after an actual step retains its earlier-filesystem provenance. -/
theorem RepairProvenance.snoc (pre post : Prefix m h .live prog start)
    (d : StepDerivation m h .live prog) (joined : post.trace = pre.trace ++ [d])
    (repair : Patch sig) (provenance : RepairProvenance pre repair) : RepairProvenance post repair := by
  intro q file found
  obtain ⟨fs, earlier, lookup⟩ := provenance q file found
  exact ⟨fs, earlierLiveFilesystems_snoc pre post d joined fs earlier, lookup⟩

/-- Every cacheable live entry retains its full E.6 package after an ordered step. -/
theorem CachePrefixProperties.entries_after_step (commands : WellFormedCommands m) (host : HostWellFormed m h)
    (pre post : Prefix m h .live prog start) (preOperational : Operational pre)
    (postOperational : Operational post) (postOrdered : ExitOrdered post.trace)
    (witnesses : WitnessMap sig) (d : StepDerivation m h .live prog)
    (allowed : h.select prog pre.final d.selection d.selected)
    (joined : post.trace = pre.trace ++ [d]) (before : pre.final = d.before) (after : post.final = d.after)
    (properties : CachePrefixProperties witnesses pre (.selected d.selection d.selected allowed)) :
    ∀ entry slot p sb, (Boundary.final : Boundary post).livePipeline entry slot →
      (Boundary.final : Boundary post).assigned entry slot p → Cacheable m p →
      FMap.get post.final.sandbox slot = some sb → EntryPrefix post .final entry slot p sb := by
  intro entry slot p sb live assigned cacheable present
  have oldLive := ((Boundary.livePipeline_after_step pre post d allowed joined entry slot).mp live).1
  have oldAssigned : (Boundary.selected d.selection d.selected allowed).assigned entry slot p := by
    obtain ⟨fs, init, entryAt, probeAt⟩ := assigned
    refine ⟨fs, init, ?_, probeAt⟩
    rw [← Boundary.entry_after_step pre post d allowed joined before oldLive.1]
    exact entryAt
  have actual : FMap.get d.after.sandbox slot = some sb := by simpa only [after] using present
  refine ⟨fun progressed => firstEnvironment_exists post.trace (.pipeline entry slot) progressed, ?_, ?_⟩
  · intro progressed env first
    rcases LiveDerivation.history_effect d.probe actual with own | foreign
    · obtain ⟨selectedProbe, head, openInput, old, hin, hout, prior, rfl⟩ := own
      have sameProbe : p = selectedProbe :=
        Boundary.selected_head_assigned host pre preOperational d.selection d.selected allowed
          entry slot p selectedProbe oldLive.1 oldAssigned head
      subst selectedProbe
      have named : componentAt post.trace pre.trace.length d = some (.pipeline entry slot) := by
        rw [joined, Boundary.componentAt_selected pre d allowed head, oldLive.1]
        rfl
      have atPos : (post.trace)[pre.trace.length]? = some d := by simp [joined]
      have envEq := FirstEnvironment.step_env host post postOperational _ env first _ d atPos named
      have call := d.probe.open_call head openInput
      have effect := d.probe.open_fs openInput
      have oldEntries := properties.entries entry slot p old oldLive oldAssigned cacheable prior
      have newAbsorbed := Operational.liveAbsorbed host post postOperational postOrdered .final
        entry slot (old.accumulate (LiveDerivation.input d.probe) (LiveDerivation.result d.probe) hin hout) live present
      have initialRepair : ∃ repair, FMap.dom repair = FMap.dom old.patch ∧
          RepairProvenance pre repair ∧
          EntryFold (m := m) p old d.selected.fs (applyPatch d.selected.fs repair) d.selected.env := by
        by_cases oldProgressed : openSteps pre.trace (.pipeline entry slot) = []
        · have zero := oldEntries.zero oldProgressed
          have initial := zero.1
          refine ⟨∅, ?_, ?_, ?_⟩
          · rw [initial]
            simp [Sandbox.initial]
          · intro q file found
            simp [FMap.get] at found
          · rw [applyPatch_empty, initial]
            exact EntryFold.initial p old.base d.selected.fs d.selected.env
        · have oldFirst := FirstEnvironment.of_snoc d joined (.pipeline entry slot) oldProgressed env first
          obtain ⟨repair, repaired⟩ := oldEntries.progressed oldProgressed env oldFirst
          refine ⟨repair, repaired.domain, repaired.provenance, ?_⟩
          simpa only [Boundary.world, envEq] using repaired.fold
      obtain ⟨repair, domain, provenance, fold⟩ := initialRepair
      obtain ⟨newRepair, repaired⟩ := RepairedEntry.advance_open commands pre post d joined after
        p cacheable old (LiveDerivation.input d.probe) (LiveDerivation.result d.probe) hin hout
        call.2 call.1 effect repair domain provenance fold newAbsorbed
      refine ⟨newRepair, ?_⟩
      simpa only [envEq] using repaired
    · obtain ⟨prior, foreignHead⟩ := foreign
      have notSelected : componentAt post.trace pre.trace.length d ≠ some (.pipeline entry slot) := by
        intro selected
        rw [joined] at selected
        obtain ⟨probe, head⟩ := componentAt_pipeline_head _ _ _ selected
        exact foreignHead probe head
      have stepsEqual : componentSteps post.trace (.pipeline entry slot) =
          componentSteps pre.trace (.pipeline entry slot) := by
        rw [joined, componentSteps_snoc]
        have diff : componentAt (pre.trace ++ [d]) pre.trace.length d ≠ some (.pipeline entry slot) := by
          simpa [joined] using notSelected
        simp [diff]
      have opensEqual : openSteps post.trace (.pipeline entry slot) = openSteps pre.trace (.pipeline entry slot) := by
        simp only [openSteps, stepsEqual]
      have oldProgressed : openSteps pre.trace (.pipeline entry slot) ≠ [] := by
        simpa [opensEqual] using progressed
      have oldFirst : FirstEnvironment pre.trace (.pipeline entry slot) env :=
        FirstEnvironment.of_snoc d joined (.pipeline entry slot) oldProgressed env first
      obtain ⟨repair, repaired⟩ :=
        (properties.entries entry slot p sb oldLive oldAssigned cacheable prior).progressed oldProgressed env oldFirst
      have denotation := EntryPrefix.foreign_denotation commands host pre post preOperational postOperational postOrdered
        (.selected d.selection d.selected allowed) entry slot p sb oldLive prior d before.symm ⟨rfl, rfl⟩ joined
        notSelected env repair repaired.denotation
      have newAbsorbed := Operational.liveAbsorbed host post postOperational postOrdered .final entry slot sb live present
      refine ⟨repair, repaired.domain, ?_, repaired.provenance.snoc pre post d joined repair, ?_⟩
      · simpa only [Boundary.world, after] using denotation
      · apply EntryFold.of_denotation commands p cacheable sb post.final.fs repair env repaired.domain newAbsorbed
        simpa only [after] using denotation
  · intro empty
    exact EntryPrefix.zero_clause host post postOperational .final entry slot p sb live present empty

/-- The current entry's recorded initialization determines the host assignment list. -/
theorem Boundary.current_entry_probes (pre : Prefix m h .live prog start)
    (selection : Selection sig) (world : World sig) (allowed : h.select prog pre.final selection world)
    (entry : Nat) (fs : FS sig) (init : PipelineInit sig)
    (current : (Boundary.selected selection world allowed).currentEntry = some entry)
    (entryAt : (Boundary.selected selection world allowed).entry entry = some (fs, init)) :
    assignedProbes pre.trace selection = some init.probes := by
  cases initializes : selection.init with
  | some fresh =>
    have index : pre.trace.length = entry := by
      simpa [Boundary.currentEntry, Boundary.selection?, initializes] using current
    subst entry
    have entryEq : some (pre.final.fs, fresh) = some (fs, init) := by
      simpa [Boundary.entry, Boundary.selection?, initializes] using entryAt
    have initEq : fresh = init := congrArg Prod.snd (Option.some.inj entryEq)
    subst init
    simp [assignedProbes, initializes]
  | none =>
    have epoch : (latestPipeline pre.trace).map Prod.fst = some entry := by
      simpa [Boundary.currentEntry, Boundary.selection?, initializes] using current
    obtain ⟨pair, latest, index⟩ := Option.map_eq_some_iff.mp epoch
    rcases pair with ⟨origin, actual⟩
    dsimp at index
    subst entry
    obtain ⟨step, atStep, actualInit⟩ := latestPipeline_origin pre.trace latest
    have bound := latestPipeline_entry_lt pre.trace latest
    have entryEq : some (step.before.fs, actual) = some (fs, init) := by
      simpa [Boundary.entry, Boundary.selection?, initializes, Nat.ne_of_lt bound, atStep, actualInit] using entryAt
    have initEq : actual = init := congrArg Prod.snd (Option.some.inj entryEq)
    subst init
    simp [assignedProbes, initializes, latest]

/-- An actual selected pipeline call belongs to a live assigned entry. -/
theorem Boundary.selected_pipeline_live (host : HostWellFormed m h)
    (pre : Prefix m h .live prog start) (operational : Operational pre)
    (d : StepDerivation m h .live prog) (allowed : h.select prog pre.final d.selection d.selected)
    {p : sig.Probe} {slot : Nat} (head : d.selection.head = .pipeline p slot)
    (sb : Sandbox sig) (present : FMap.get d.selected.sandbox slot = some sb) :
    ∃ entry, (Boundary.selected d.selection d.selected allowed).livePipeline entry slot ∧
      (Boundary.selected d.selection d.selected allowed).assigned entry slot p := by
  have allocation := Operational.slotAllocation host pre operational (.selected d.selection d.selected allowed)
  have buffer := ProbeDerivation.pipeline_buffer_present (head ▸ d.probe)
  change slot ∈ FMap.dom (Boundary.selected d.selection d.selected allowed).world.buffer at buffer
  rw [allocation.buffers] at buffer
  obtain ⟨entry, current, domain, noClose⟩ := buffer
  have captured := Operational.capturedEntries host pre operational (.selected d.selection d.selected allowed)
  obtain ⟨actual, fs, init, actualCurrent, entryAt, _, _⟩ := captured slot sb present
  rw [current] at actualCurrent
  have same : actual = entry := Option.some.inj actualCurrent.symm
  subst actual
  have assignedList := Boundary.current_entry_probes pre d.selection d.selected allowed entry fs init current entryAt
  have discipline := host.selectionDiscipline .live prog start pre operational d.selection d.selected allowed
  have law := discipline.2.2.2.2
  rw [head] at law
  obtain ⟨probes, listAt, probeAt⟩ := law.2.2.2
  rw [assignedList] at listAt
  cases Option.some.inj listAt
  exact ⟨entry, ⟨current, domain, noClose⟩, ⟨fs, init, entryAt, probeAt⟩⟩

/-- A progressed selected component uses its first actual environment. -/
theorem FirstEnvironment.selected_env (host : HostWellFormed m h)
    (pre : Prefix m h .live prog start) (operational : Operational pre)
    (d : StepDerivation m h .live prog) (allowed : h.select prog pre.final d.selection d.selected)
    (entry slot : Nat) (p : sig.Probe) (head : d.selection.head = .pipeline p slot)
    (live : (Boundary.selected d.selection d.selected allowed).livePipeline entry slot)
    (env : Env sig) (first : FirstEnvironment pre.trace (.pipeline entry slot) env) :
    d.selected.env = env := by
  obtain ⟨firstStep, firstAt, envEq⟩ := first
  have member : firstStep ∈ componentSteps pre.trace (.pipeline entry slot) := List.mem_of_head? firstAt
  have entryLt : entry < pre.trace.length := by
    by_contra notLt
    have fresh := componentSteps_fresh pre.trace entry slot (Nat.le_of_not_gt notLt)
    simp [fresh] at member
  have noInit : d.selection.init = none := by
    cases initializes : d.selection.init with
    | none => rfl
    | some init =>
      have equal : pre.trace.length = entry := by
        simpa [Boundary.currentEntry, Boundary.selection?, initializes] using live.1
      exact False.elim (Nat.lt_irrefl _ (equal ▸ entryLt))
  have current : (latestPipeline pre.trace).map Prod.fst = some entry := by
    simpa [Boundary.currentEntry, Boundary.selection?, noInit] using live.1
  have currentSlot : liveComponent pre.trace slot = some (.pipeline entry slot) := by
    unfold liveComponent
    obtain ⟨pair, latest, index⟩ := Option.map_eq_some_iff.mp current
    rcases pair with ⟨origin, init⟩
    dsimp at index
    subst origin
    simp [latest]
  have historical : LivePipelineComponent pre.trace entry slot :=
    ⟨Boundary.pipelineDomain_old pre d.selection d.selected allowed entryLt live.2.1, live.2.2⟩
  have selected := host.componentSelectionEnvironments .live prog start pre operational
    d.selection d.selected allowed p slot entry firstStep noInit head historical currentSlot member
  exact selected.trans envEq

/-- Every selected cacheable entry has a repair and fold for the actual call, including its first call. -/
theorem EntryPrefix.selected_fold (host : HostWellFormed m h)
    (pre : Prefix m h .live prog start) (operational : Operational pre)
    (d : StepDerivation m h .live prog) (allowed : h.select prog pre.final d.selection d.selected)
    (entry slot : Nat) (p : sig.Probe) (sb : Sandbox sig)
    (head : d.selection.head = .pipeline p slot)
    (live : (Boundary.selected d.selection d.selected allowed).livePipeline entry slot)
    (entryPrefix : EntryPrefix pre (.selected d.selection d.selected allowed) entry slot p sb) :
    ∃ repair, FMap.dom repair = FMap.dom sb.patch ∧ RepairProvenance pre repair ∧
      EntryFold (m := m) p sb d.selected.fs (applyPatch d.selected.fs repair) d.selected.env := by
  by_cases empty : openSteps pre.trace (.pipeline entry slot) = []
  · obtain ⟨initial, fold⟩ := entryPrefix.zero empty
    refine ⟨∅, ?_, ?_, ?_⟩
    · rw [initial]
      simp [Sandbox.initial]
    · intro q file found
      simp [FMap.get] at found
    · have selected : SelectedAt (.selected d.selection d.selected allowed) p slot d.selected.env := ⟨head, rfl⟩
      have result := fold d.selected.env selected
      simpa only [Boundary.world, applyPatch_empty] using result.2
  · obtain ⟨env, first⟩ := entryPrefix.firstEnvironment empty
    have selectedEnv := FirstEnvironment.selected_env host pre operational d allowed entry slot p head live env first
    obtain ⟨repair, repaired⟩ := entryPrefix.progressed empty env first
    refine ⟨repair, repaired.domain, repaired.provenance, ?_⟩
    simpa only [Boundary.world, selectedEnv] using repaired.fold

end
end IncrPP
end Incr

/-!
# Actual cache updates of live rules

Only the two cacheable miss rules can store a memo. Their retained calls,
keys, and accumulated results supply the witness obligations.
-/

namespace Incr.IncrPP

noncomputable section

variable {sig : Signature} {m : CommandModel sig}

/-- A pipeline miss retains the exact complete call and accumulated memo. -/
def PipelineMemoCause (w : World sig) (head : Head sig) (key : Key sig) (memo : Memo sig) : Prop :=
  ∃ (p : sig.Probe) (i : Nat) (sb : Sandbox sig) (s : Bytes) (r : Result sig) (es : Nat),
    ∃ (hin : sb.input.flag = .open) (hout : sb.output.flag = .open) (hflag : r.output.flag = .eof),
    head = .pipeline p i ∧ Cacheable m p ∧
      FMap.get w.sandbox i = some sb ∧ m.denotes p ⟨s, .eof⟩ w.fs w.env r ∧ r.status = some es ∧
      key = cacheKey m p w.env (sb.input ++'hin ⟨s, .eof⟩) ∧
      memo = accumulatedMemo sb ⟨s, .eof⟩ r es hin hout hflag

/-- A standalone miss retains its exact whole-input result and key. -/
def StandaloneMemoCause (w : World sig) (head : Head sig) (key : Key sig) (memo : Memo sig) : Prop :=
  ∃ (p : sig.Probe) (s : Bytes) (r : Result sig) (es : Nat), ∃ (hflag : r.output.flag = .eof),
    head = .standalone p ∧ Cacheable m p ∧ m.denotes p ⟨s, .eof⟩ w.fs w.env r ∧
      r.status = some es ∧ key = cacheKey m p w.env ⟨s, .eof⟩ ∧
      memo = ⟨es, r.patch, r.reads, r.writes, r.output, hflag⟩

/-- All other rules retain the cache; miss policies retain their actual stored-memo evidence. -/
theorem LiveDerivation.cache_effect {before after : World sig} {head : Head sig}
    {returned : Option Chunk} (d : LiveDerivation m before head after returned) :
    after.cache = before.cache ∨ ∃ key memo, CacheUpdate before.cache key memo after.cache ∧
      (PipelineMemoCause (m := m) before head key memo ∨ StandaloneMemoCause (m := m) before head key memo) := by
  cases d
  all_goals try exact Or.inl rfl
  case cacheCloseMiss =>
    apply Or.inr
    refine ⟨_, _, by assumption, Or.inl ?_⟩
    refine ⟨_, _, _, _, _, _, _, _, _, rfl, by assumption, by assumption, by assumption, by assumption, rfl, rfl⟩
  case cacheStandaloneMiss =>
    apply Or.inr
    refine ⟨_, _, by assumption, Or.inr ?_⟩
    refine ⟨_, _, _, _, _, rfl, by assumption, by assumption, by assumption, rfl, rfl⟩

variable {h : Host sig} {prog : sig.Prog} {start : World sig}

/-- The actual miss choices preserve one valid provenance witness for every remaining memo. -/
theorem CachePrefixProperties.memos_after_step (host : HostWellFormed m h)
    (pre post : Prefix m h .live prog start) (operational : Operational pre)
    (witnesses : WitnessMap sig) (d : StepDerivation m h .live prog)
    (allowed : h.select prog pre.final d.selection d.selected)
    (joined : post.trace = pre.trace ++ [d]) (after : post.final = d.after)
    (properties : CachePrefixProperties witnesses pre (.selected d.selection d.selected allowed)) :
    CacheWitnessed (m := m) witnesses post.records post.final.cache := by
  have old : CacheWitnessed (m := m) witnesses
      (Boundary.selected d.selection d.selected allowed).records d.selected.cache := by
    intro key memo found
    obtain ⟨fs, witness, provenance⟩ := properties.memos key memo found
    exact ⟨fs, witness, ((Boundary.selected d.selection d.selected allowed).recordedWitnessProvenance_iff
      witnesses fs).mp provenance⟩
  have more := Boundary.records_snoc pre post (.selected d.selection d.selected allowed) d joined rfl
  rcases d.probe.cache_effect with same | ⟨key, memo, update, cause⟩
  · apply CacheWitnessed.subcache old more
    intro lookupKey lookupMemo lookup
    simpa only [after, same] using lookup
  · have stored : ∃ fs, EntryWitness m key memo fs ∧ WitnessProvenance witnesses post.records fs := by
      rcases cause with pipeline | standalone
      · obtain ⟨p, slot, sb, bytes, result, es, hin, hout, flag, head, cacheable,
          present, call, status, rfl, rfl⟩ := pipeline
        obtain ⟨entry, live, assigned⟩ := Boundary.selected_pipeline_live host pre operational d allowed head sb present
        have entryPrefix := properties.entries entry slot p sb live assigned cacheable present
        obtain ⟨repair, _, provenance, fold⟩ := EntryPrefix.selected_fold host pre operational d allowed
          entry slot p sb head live entryPrefix
        obtain ⟨fs, witness, recorded⟩ := CacheWitnessed.accumulated_certificate witnesses pre
          (.selected d.selection d.selected allowed) p sb ⟨bytes, .eof⟩ result es hin hout flag status
          rfl cacheable d.selected.env repair provenance fold call
        exact ⟨fs, witness, recorded.mono more⟩
      · obtain ⟨p, bytes, result, es, flag, head, cacheable, call, status, rfl, rfl⟩ := standalone
        have certificate : m.denotes p ⟨bytes, .eof⟩ d.selected.fs d.selected.env
            (⟨es, result.patch, result.reads, result.writes, result.output, flag⟩ : Memo sig).result := by
          cases result with
          | mk status' patch reads writes output =>
            have same : status' = some es := status
            subst status'
            exact call
        refine ⟨d.selected.fs, ⟨p, d.selected.env, ⟨bytes, .eof⟩, cacheable, rfl, rfl, certificate⟩, Or.inr ?_⟩
        intro q file lookup
        exact more _ (Boundary.fs_record pre (.selected d.selection d.selected allowed) q file lookup)
    have update' : CacheUpdate d.selected.cache key memo post.final.cache := by simpa only [after] using update
    exact CacheWitnessed.update old more update' stored

/-- E.6's entire joint package is preserved at each ordered operational endpoint. -/
theorem CachePrefixProperties.final (host : HostWellFormed m h) (commands : WellFormedCommands m)
    (pre : Prefix m h .live prog start) (operational : Operational pre) (ordered : ExitOrdered pre.trace)
    (initialCache : WellFormedCache m start.cache) (witnesses : WitnessMap sig)
    (chosen : WitnessesFor m start.cache witnesses) : CachePrefixProperties witnesses pre .final := by
  apply Operational.snoc_induction
    (fun pre => ExitOrdered pre.trace → CachePrefixProperties witnesses pre .final) ?_ ?_ pre operational ordered
  · intro pre _ empty _
    have connected := pre.connected
    rw [empty] at connected
    have endpoint := (Connected.nil_iff start pre.final).mp connected
    constructor
    · simpa [Boundary.world, endpoint] using initialCache
    · intro entry slot p sb _ _ _ present
      simp [Boundary.world, endpoint, pre.initial.2.1, FMap.get] at present
    · intro key memo found
      have initial : CacheWitnessed (m := m) witnesses pre.records start.cache := CacheWitnessed.initial chosen
      obtain ⟨fs, witness, provenance⟩ := initial key memo (by
        simpa [Boundary.world, endpoint] using found)
      exact ⟨fs, witness, ((Boundary.final : Boundary pre).recordedWitnessProvenance_iff
        witnesses fs).mpr provenance⟩
  · intro short post d shortOperational postOperational joined before after ih postOrdered
    have shortOrdered : ExitOrdered short.trace := by
      apply ExitOrdered.of_append short.trace [d]
      simpa only [joined] using postOrdered
    have allowed : h.select prog short.final d.selection d.selected := by
      simpa only [before] using d.host
    have selected := CachePrefixProperties.selected host short shortOperational witnesses
      (ih shortOrdered) d.selection d.selected allowed
    have memos := CachePrefixProperties.memos_after_step host short post shortOperational witnesses d allowed
      joined after selected
    constructor
    · exact memos.wellFormed
    · exact CachePrefixProperties.entries_after_step commands host short post shortOperational postOperational
        postOrdered witnesses d allowed joined before after selected
    · intro key memo found
      obtain ⟨fs, witness, provenance⟩ := memos key memo found
      exact ⟨fs, witness, ((Boundary.final : Boundary post).recordedWitnessProvenance_iff
        witnesses fs).mpr provenance⟩

/-- E.6's package also holds at every permitted selection, with no future-step premise. -/
theorem CachePrefixProperties.all_boundaries (host : HostWellFormed m h) (commands : WellFormedCommands m)
    (pre : Prefix m h .live prog start) (operational : Operational pre) (ordered : ExitOrdered pre.trace)
    (initialCache : WellFormedCache m start.cache) (witnesses : WitnessMap sig)
    (chosen : WitnessesFor m start.cache witnesses) :
    ∀ b : Boundary pre, CachePrefixProperties witnesses pre b := by
  have endpoint := CachePrefixProperties.final host commands pre operational ordered initialCache witnesses chosen
  intro b
  cases b with
  | final => exact endpoint
  | selected selection world allowed =>
    exact CachePrefixProperties.selected host pre operational witnesses endpoint selection world allowed

end
end IncrPP
end Incr

/-!
# E.6: live prefixes and cache preservation

The numbered statement combines the joint endpoint induction with the
separate permitted-selection argument. Its printed assumptions stay explicit.
-/

namespace Incr.IncrPP

open Incr
noncomputable section
variable {sig : Signature} {m : CommandModel sig} {h : Host sig}
  {prog : sig.Prog} {start : World sig}

-- Keep the paper's global hypotheses explicit in the public statement.
set_option linter.unusedVariables false in
/-- E.6: endpoint or permitted selection, fixed initial choices, no joint-witness premise. -/
theorem prefixes_and_cache_preservation (shape : DenotationShape m) (commands : WellFormedCommands m)
    (host : HostWellFormed m h) (hash : HashInjective m)
    (pre : Prefix m h .live prog start) (operational : Operational pre) (ordered : ExitOrdered pre.trace)
    (cache : WellFormedCache m start.cache) (witnesses : WitnessMap sig)
    (chosen : WitnessesFor m start.cache witnesses) :
    ∀ b : Boundary pre, CachePrefixProperties witnesses pre b := by
  exact CachePrefixProperties.all_boundaries host commands pre operational ordered cache witnesses chosen

end
end IncrPP
end Incr
