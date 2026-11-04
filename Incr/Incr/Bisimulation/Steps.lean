import Incr.Incr.Bisimulation.StepMatching
import Incr.Incr.Bisimulation.Basis
import Incr.Incr.Support.RecordInventory
import Incr.Incr.Bisimulation.OverlayUpdates
import Incr.Incr.Bisimulation.PrefixProperties

/-!
# Strong bisimulation (`thm:paper-bisimulation`): both admissible step simulations

The proofs construct actual target derivations and prove timestamp provenance,
isolation, and every successor relation field. They use the proved preservation
and prefix results (`lem:paper-overlay`--`lem:paper-bisim-prefix`), not the public
`thm:paper-bisimulation` or `thm:paper-sound` theorems.
-/

open Incr
namespace Incr.Incr.C8Steps

noncomputable section

variable {sig : Signature} {m : CommandModel sig} {h : Host sig}
  {prog : sig.Prog} {start : World sig}

/-- Restriction preserves observed filesystem agreement. -/
theorem approx_restrict {fs target : FS sig} (agreement : FSApprox fs target) (Q : Set sig.Path) :
    FSApprox (fs ↾ Q) (target ↾ Q) := by
  classical
  apply FSApprox.of_contents
  intro q
  simp only [FMap.get_restrict]
  split
  · exact agreement.contents q
  · rfl

/-- Agreement on a larger path set supplies agreement on recorded dependencies. -/
theorem approx_restrict_subset {fs target : FS sig} {Q D : Set sig.Path}
    (agreement : FSApprox (fs ↾ Q) (target ↾ Q)) (subset : D ⊆ Q) :
    FSApprox (fs ↾ D) (target ↾ D) := by
  classical
  apply FSApprox.of_contents
  intro q
  simp only [FMap.get_restrict]
  split_ifs with member
  · have equality := agreement.contents q
    simpa [FMap.get_restrict, subset member] using equality
  · rfl

/-- A final step belongs to the invocation selected at its recorded boundary. -/
theorem snoc_member {executor : Executor} (trace : Trace m h executor prog)
    (d : StepDerivation m h executor prog) {k : Component}
    (position : componentAt (trace ++ [d]) trace.length d = some k) :
    d ∈ componentSteps (trace ++ [d]) k := by
  rw [componentSteps_snoc]
  exact List.mem_append_right _ (by simp [position])

/-- The full successor access set contains every dependency of the new result. -/
theorem snoc_dependencies {executor : Executor} (trace : Trace m h executor prog)
    (d : StepDerivation m h executor prog) {k : Component}
    (position : componentAt (trace ++ [d]) trace.length d = some k) :
    FMap.dom (ProbeDerivation.result d.probe).reads ∪
      FMap.dom (ProbeDerivation.result d.probe).writes ⊆ componentAccesses (trace ++ [d]) k := by
  intro q member
  exact Or.inl ⟨d, snoc_member trace d position, member⟩

/-- Successor isolation excludes the whole successor access set from older writes. -/
theorem source_exclusion {executor : Executor} (trace : Trace m h executor prog)
    (d : StepDerivation m h executor prog) (isolated : Isolated (trace ++ [d]))
    (entry i j : Nat) (distinct : i ≠ j) :
    Disjoint (componentAccesses (trace ++ [d]) (.pipeline entry i))
      (componentWrites trace (.pipeline entry j)) := by
  apply Set.disjoint_left.mpr
  intro q access written
  apply Set.disjoint_left.mp (isolated entry j i distinct.symm)
  · obtain ⟨old, member, path⟩ := written
    exact ⟨old, C9.componentSteps_append_subset trace [d] _ old member, path⟩
  · exact access

/-- Source isolation includes every other component, including closed slots. -/
theorem source_other_exclusion (trace : Trace m h .incr prog)
    (d : StepDerivation m h .incr prog) (isolated : Isolated (trace ++ [d]))
    (entry i : Nat) :
    Disjoint (componentAccesses (trace ++ [d]) (.pipeline entry i))
      (otherWrites trace entry i) := by
  apply Set.disjoint_left.mpr
  intro q access written
  obtain ⟨j, distinct, member⟩ := PrefixProperties.mem_otherWrites.mp written
  exact Set.disjoint_left.mp (source_exclusion trace d isolated entry i j distinct.symm) access member

/-- `lem:paper-bisim-prefix` and actual source-edge isolation supply the call
comparison for a pipeline call. -/
theorem forward_pipeline_agreement (host : HostWellFormed m h)
    {witnesses : WitnessMap sig} {incr : Prefix m h .incr prog start}
    {vanilla : Prefix m h .vanilla prog start} (related : BisimRelated witnesses incr vanilla)
    (properties : BisimPrefixProperties witnesses incr) (d : StepDerivation m h .incr prog)
    (before : d.before = incr.final) (isolated : Isolated (incr.trace ++ [d]))
    {sv : Selection sig} {wv : World sig} (chosen : h.select prog vanilla.final sv wv)
    {p : sig.Probe} {i : Nat} {sb : Sandbox sig}
    (head : d.selection.head = .pipeline p i) (sandbox : FMap.get d.selected.sandbox i = some sb) :
    ∃ entry init, selectedPipeline incr.trace d.selection = some (entry, init) ∧
      FSApprox (sb.view ↾ componentAccesses (incr.trace ++ [d]) (.pipeline entry i))
        (wv.fs ↾ componentAccesses (incr.trace ++ [d]) (.pipeline entry i)) ∧
      componentAt (incr.trace ++ [d]) incr.trace.length d = some (.pipeline entry i) := by
  have hostD : h.select prog incr.final d.selection d.selected := before ▸ d.host
  have slices := properties.2.2 d.selection d.selected hostD
  obtain ⟨entry, init, current, slice, accounting⟩ := slices i sb sandbox
  refine ⟨entry, init, current, ?_, ?_⟩
  · exact call_agreement slices (selected_overlay host related hostD chosen)
      i sb sandbox entry init current _ (source_other_exclusion incr.trace d isolated entry i)
  · rw [componentAt_snoc_last, head]
    simp only [selectedComponent, current, Option.map_some]

/-- Exact agreement on dependency paths preserves validation. -/
theorem valid_of_restrict {reads : Reads sig} {writes : Writes sig} {fs target : FS sig}
    {Q : Set sig.Path} (valid : Valid m reads writes fs)
    (same : fs ↾ Q = target ↾ Q) (covered : FMap.dom reads ∪ FMap.dom writes ⊆ Q) :
    Valid m reads writes target := by
  classical
  have get q (member : q ∈ FMap.dom reads ∪ FMap.dom writes) :
      FMap.get fs q = FMap.get target q := by
    have equality := congrArg (fun fs => FMap.get fs q) same
    simpa [FMap.get_restrict, covered member] using equality
  refine ⟨?_, ?_, ?_⟩
  · intro q member
    obtain ⟨file, found⟩ := Finmap.mem_iff.mp (Finmap.mem_keys.mp (valid.1 member))
    apply Finmap.mem_keys.mpr
    apply Finmap.mem_iff.mpr
    exact ⟨file, (get q member).symm.trans found⟩
  · intro q t file read found
    have member : q ∈ FMap.dom reads ∪ FMap.dom writes :=
      Or.inl (Finmap.mem_keys.mpr (Finmap.mem_iff.mpr ⟨t, read⟩))
    exact valid.2.1 q t file read ((get q member).trans found)
  · intro q hash file write found
    have member : q ∈ FMap.dom reads ∪ FMap.dom writes :=
      Or.inr (Finmap.mem_keys.mpr (Finmap.mem_iff.mpr ⟨hash, write⟩))
    exact valid.2.2 q hash file write ((get q member).trans found)

/-- An actual source successor makes its selected snapshots consistent with every
`lem:paper-bisim-prefix` cache witness from the preceding prefix. -/
theorem source_witness_timestamps {witnesses : WitnessMap sig}
    {pre full : Prefix m h .incr prog start} (admitted : Admissible witnesses full)
    (properties : BisimPrefixProperties witnesses pre)
    (d : StepDerivation m h .incr prog) (trace : full.trace = pre.trace ++ [d])
    {key : Key sig} {memo : Memo sig} (entry : FMap.get pre.final.cache key = some memo)
    {snapshot : FS sig} (retained : recordOfFS snapshot ∈ d.paperRecords) :
    ∃ historical, EntryWitness m key memo historical ∧
      TimestampConsistent ({recordOfFS historical} ∪ {recordOfFS snapshot}) := by
  obtain ⟨p, env, witness, cacheable, eof, cacheKey, call, provenance, _⟩ :=
    properties.1 key memo entry
  refine ⟨witness.fs, ⟨p, env, witness.input, cacheable, eof, cacheKey, call⟩, ?_⟩
  apply admitted.timestamps.mono
  intro record member
  rcases member with historical | current
  · have same : record = recordOfFS witness.fs := Set.mem_singleton_iff.mp historical
    subst record
    rcases provenance with initial | recorded
    · exact Or.inr initial
    · rcases recorded with initial | ⟨old, oldAt, oldRecord⟩
      · exact Or.inl (Or.inl initial)
      · exact Or.inl (Or.inr ⟨old, by rw [trace]; exact List.mem_append_left _ oldAt, oldRecord⟩)
  · have same : record = recordOfFS snapshot := Set.mem_singleton_iff.mp current
    subst record
    exact Or.inl (Or.inr ⟨d, by rw [trace]; simp, retained⟩)

/-- The local source record inventory for either actual edge direction. -/
def EdgeRecords {executor : Executor} (pre : Prefix m h executor prog start)
    (d : StepDerivation m h executor prog) (witnesses : WitnessMap sig) : Records sig :=
  pre.records ++ d.records ++ witnessRecords witnesses

/-- Actual paired result accounting is stated before appending the target record. -/
def CallPaths (trace : Trace m h .incr prog) (d : StepDerivation m h .incr prog)
    (r : Result sig) : Prop :=
  ∀ k, componentAt (trace ++ [d]) trace.length d = some k →
    componentWrites trace k ∪ FMap.dom (ProbeDerivation.result d.probe).patch =
      componentWrites trace k ∪ FMap.dom r.patch ∧
    componentAccesses trace k ∪ FMap.dom (ProbeDerivation.result d.probe).patch ∪
        FMap.dom (ProbeDerivation.result d.probe).reads ∪
        FMap.dom (ProbeDerivation.result d.probe).writes =
      componentAccesses trace k ∪ FMap.dom r.patch ∪ FMap.dom r.reads ∪ FMap.dom r.writes

/-- Equal result domains give the exact cumulative accounting for executing calls. -/
theorem call_paths_domains (trace : Trace m h .incr prog) (d : StepDerivation m h .incr prog)
    (r : Result sig)
    (patch : FMap.dom (ProbeDerivation.result d.probe).patch = FMap.dom r.patch)
    (reads : FMap.dom (ProbeDerivation.result d.probe).reads = FMap.dom r.reads)
    (writes : FMap.dom (ProbeDerivation.result d.probe).writes = FMap.dom r.writes) :
    CallPaths trace d r := by
  intro k _
  rw [patch, reads, writes]
  exact ⟨rfl, rfl⟩

/-- Executing calls match their selected patch. A pipeline hit matches the
complete memo against the accumulated patch followed by its closing call. -/
def CallPatch (d : StepDerivation m h .incr prog) (r : Result sig) : Prop :=
  match ProbeDerivation.callFS d.probe, d.selection.head with
  | none, .pipeline _ i => ∀ sb, FMap.get d.selected.sandbox i = some sb →
      PatchApprox (sb.patch ⊎ r.patch) (ProbeDerivation.result d.probe).patch
  | _, _ => PatchApprox r.patch (ProbeDerivation.result d.probe).patch

theorem patch_trans {a b c : Patch sig} (ab : PatchApprox a b) (bc : PatchApprox b c) :
    PatchApprox a c :=
  ⟨ab.1.trans bc.1, fun q hq => (ab.2 q hq).trans (bc.2 q (ab.1 ▸ hq))⟩

theorem patch_symm {a b : Patch sig} (ab : PatchApprox a b) : PatchApprox b a :=
  ⟨ab.1.symm, fun q hq => (ab.2 q (ab.1.symm ▸ hq)).symm⟩

/-- Dependency transport preserves the cumulative path certificate. -/
theorem call_paths_transport {trace : Trace m h .incr prog} {d : StepDerivation m h .incr prog}
    {r r' : Result sig} (paths : CallPaths trace d r)
    (patch : PatchApprox r'.patch r.patch) (reads : FMap.dom r'.reads = FMap.dom r.reads)
    (writes : r'.writes = r.writes) : CallPaths trace d r' := by
  intro k position
  obtain ⟨hw, ha⟩ := paths k position
  rw [patch.1, reads, writes]
  exact ⟨hw, ha⟩

/-- Patch transport also preserves the complete-memo certificate for hits. -/
theorem call_patch_transport {d : StepDerivation m h .incr prog} {r r' : Result sig}
    (matched : CallPatch d r) (patch : PatchApprox r'.patch r.patch) : CallPatch d r' := by
  unfold CallPatch at matched ⊢
  split at matched
  · intro sb present
    exact patch_trans ((patch_algebra (sig := sig)).2.2.2.2.1 _ _ _ _
      ⟨rfl, fun _ _ => rfl⟩ patch) (matched sb present)
  · exact patch_trans patch matched

def CallLocation (head : Head sig) (w : World sig) (fs : FS sig) : Prop :=
  match head with
  | .standalone _ => fs = w.fs
  | .pipeline _ i => ∃ sb, FMap.get w.sandbox i = some sb ∧ fs = sb.view

/-- The actual executing Incr rule retains its denotation and call filesystem. -/
theorem incr_executing {w after : World sig} {head : Head sig} {out : Option Chunk}
    (d : IncrDerivation m w head after out) (fs : FS sig)
    (executes : IncrDerivation.callFS d = some fs) :
    m.denotes head.probe (IncrDerivation.input d) fs w.env (IncrDerivation.result d) ∧
      IncrDerivation.produced d = (IncrDerivation.result d).output ∧
      CallLocation head w fs := by
  cases d <;> simp only [IncrDerivation.callFS, Option.some.injEq] at executes
  all_goals first
    | contradiction
    | (subst fs
       simp_all [IncrDerivation.input, IncrDerivation.result, IncrDerivation.produced,
         Head.probe, CallLocation])

/-- No sandbox patch is pending at a selected standalone call. -/
theorem standalone_selected_agreement (host : HostWellFormed m h)
    {witnesses : WitnessMap sig} {incr : Prefix m h .incr prog start}
    {vanilla : Prefix m h .vanilla prog start} (related : BisimRelated witnesses incr vanilla)
    {si sv : Selection sig} {wi wv : World sig}
    (hi : h.select prog incr.final si wi) (hv : h.select prog vanilla.final sv wv)
    {p : sig.Probe} (head : si.head = .standalone p) : FSApprox wi.fs wv.fs := by
  have discipline := host.selectionDiscipline _ _ _ incr related.incrAdmissible.operational _ _ hi
  have standalone := discipline.2.2.2.2
  rw [head] at standalone
  have overlay := selected_overlay host related hi hv
  have empty : pendingPatch wi = ∅ := pending_zero wi (by simp [standalone.2.2.2.2.1, FMap.get])
  rw [empty, (patch_algebra (sig := sig)).2.1] at overlay
  exact FSApprox.of_contents (fun q => (overlay.contents q).symm)

/-- `lem:paper-bisim-prefix` and the given source edge provide dependency
agreement for every executing Incr call, with no terminating continuation
assumption. -/
theorem executing_forward_agreement (host : HostWellFormed m h)
    {witnesses : WitnessMap sig} {incr : Prefix m h .incr prog start}
    {vanilla : Prefix m h .vanilla prog start} (related : BisimRelated witnesses incr vanilla)
    (properties : BisimPrefixProperties witnesses incr) (d : StepDerivation m h .incr prog)
    (before : d.before = incr.final) (isolated : Isolated (incr.trace ++ [d]))
    {sv : Selection sig} {wv : World sig} (chosen : h.select prog vanilla.final sv wv)
    (fs : FS sig) (executes : ProbeDerivation.callFS d.probe = some fs) :
    FSApprox (fs ↾ (FMap.dom (ProbeDerivation.result d.probe).reads ∪
      FMap.dom (ProbeDerivation.result d.probe).writes))
      (wv.fs ↾ (FMap.dom (ProbeDerivation.result d.probe).reads ∪
      FMap.dom (ProbeDerivation.result d.probe).writes)) := by
  have details := incr_executing d.probe fs executes
  have alternatives : (∃ p, d.selection.head = .standalone p) ∨
      (∃ p i, d.selection.head = .pipeline p i) := by
    cases d.selection.head
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inr ⟨_, _, rfl⟩
  rcases alternatives with ⟨p, head⟩ | ⟨p, i, head⟩
  · have live : fs = d.selected.fs := by simpa only [CallLocation, head] using details.2.2
    rw [live]
    exact approx_restrict (standalone_selected_agreement host related (before ▸ d.host) chosen head) _
  · obtain ⟨sb, sandbox, live⟩ : ∃ sb, FMap.get d.selected.sandbox i = some sb ∧ fs = sb.view := by
      simpa only [CallLocation, head] using details.2.2
    obtain ⟨entry, init, current, agreement, position⟩ :=
      forward_pipeline_agreement host related properties d before isolated chosen head sandbox
    rw [live]
    exact approx_restrict_subset agreement (snoc_dependencies incr.trace d position)

/-- Every source call certificate has its status, output, path accounting, and
complete-memo patch equation. -/
def ForwardWitness (trace : Trace m h .incr prog) (d : StepDerivation m h .incr prog)
    (target : World sig) : Prop :=
  ∃ fs r, m.denotes d.selection.head.probe (ProbeDerivation.input d.probe) fs d.selected.env r ∧
    FSApprox (fs ↾ (FMap.dom r.reads ∪ FMap.dom r.writes))
      (target.fs ↾ (FMap.dom r.reads ∪ FMap.dom r.writes)) ∧
    r.status = (ProbeDerivation.result d.probe).status ∧
    r.output = ProbeDerivation.produced d.probe ∧ CallPaths trace d r ∧ CallPatch d r

/-- Actual non-hit constructors supply forward witnesses directly. -/
theorem executing_forward_witness (host : HostWellFormed m h)
    {witnesses : WitnessMap sig} {incr : Prefix m h .incr prog start}
    {vanilla : Prefix m h .vanilla prog start} (related : BisimRelated witnesses incr vanilla)
    (properties : BisimPrefixProperties witnesses incr) (d : StepDerivation m h .incr prog)
    (before : d.before = incr.final) (isolated : Isolated (incr.trace ++ [d]))
    {sv : Selection sig} {wv : World sig} (chosen : h.select prog vanilla.final sv wv)
    (fs : FS sig) (executes : ProbeDerivation.callFS d.probe = some fs) :
    ForwardWitness incr.trace d wv := by
  have details := incr_executing d.probe fs executes
  refine ⟨fs, ProbeDerivation.result d.probe, details.1,
    executing_forward_agreement host related properties d before isolated chosen fs executes,
    rfl, details.2.1.symm, call_paths_domains _ _ _ rfl rfl rfl, ?_⟩
  simp only [CallPatch, executes]
  exact ⟨rfl, fun _ _ => rfl⟩

/-- Historical writes remain accesses after the new source step. -/
theorem old_writes_accesses {executor : Executor} (trace : Trace m h executor prog)
    (d : StepDerivation m h executor prog) (k : Component) :
    componentWrites trace k ⊆ componentAccesses (trace ++ [d]) k := by
  rintro q ⟨old, member, path⟩
  exact Or.inr ⟨old, C9.componentSteps_append_subset trace [d] k old member, path⟩

/-- The source hit's actual isolation and `lem:paper-bisim-prefix` frame discharge
the `lem:paper-hit-completion` base-validity
and witness-consistency premises. The reconstructed call is not an execution record. -/
theorem pipeline_hit_forward_witness (shape : DenotationShape m) (commands : WellFormedCommands m)
    (key : HashInjective m) (host : HostWellFormed m h) (cache : WellFormedCache m start.cache)
    {witnesses : WitnessMap sig} {incr full : Prefix m h .incr prog start}
    {vanilla : Prefix m h .vanilla prog start} (related : BisimRelated witnesses incr vanilla)
    (properties : BisimPrefixProperties witnesses incr) (admitted : Admissible witnesses full)
    (d : StepDerivation m h .incr prog) (before : d.before = incr.final)
    (trace : full.trace = incr.trace ++ [d])
    {sv : Selection sig} {wv : World sig} (chosen : h.select prog vanilla.final sv wv)
    {p : sig.Probe} {i : Nat} {sb : Sandbox sig} {s : Bytes} {memo : Memo sig}
    (head : d.selection.head = .pipeline p i) (hit : CacheCloseHitApplication m d.selected p i sb s memo)
    (input : ProbeDerivation.input d.probe = ⟨s, .eof⟩)
    (result : ProbeDerivation.result d.probe = memo.result)
    (produced : ProbeDerivation.produced d.probe = ⟨hit.tail, .eof⟩)
    (noCall : ProbeDerivation.callFS d.probe = none) : ForwardWitness incr.trace d wv := by
  have hostD : h.select prog incr.final d.selection d.selected := before ▸ d.host
  have isolated : Isolated (incr.trace ++ [d]) := trace ▸ admitted.isolated
  have slices := properties.2.2 _ _ hostD
  obtain ⟨entry, init, current, slice, accounting⟩ := slices i sb hit.sandbox
  have position : componentAt (incr.trace ++ [d]) incr.trace.length d = some (.pipeline entry i) := by
    rw [componentAt_snoc_last, head]
    simp only [selectedComponent, current, Option.map_some]
  let Q := componentAccesses (incr.trace ++ [d]) (.pipeline entry i)
  have dependencyBounds : FMap.dom memo.reads ∪ FMap.dom memo.writes ⊆ Q := by
    simpa only [result, Memo.result] using snoc_dependencies incr.trace d position
  have excluded : Disjoint Q (otherWrites incr.trace entry i) :=
    source_other_exclusion incr.trace d isolated entry i
  have validBase : Valid m memo.reads memo.writes sb.base :=
    valid_of_restrict hit.valid (slice.2.2 Q excluded).symm dependencyBounds
  have discipline := host.selectionDiscipline _ _ _ incr related.incrAdmissible.operational _ _ hostD
  have oldEntry : FMap.get incr.final.cache
      (cacheKey m p d.selected.env (sb.input ++'hit.inputOpen ⟨s, .eof⟩)) = some memo := by
    simpa only [discipline.2.2.1] using hit.entry
  have retained : recordOfFS sb.base ∈ d.paperRecords := by
    have member := (sandbox_mem_paperRecords hit.sandbox).1
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr member))))
  obtain ⟨historical, witness, timestamps⟩ :=
    source_witness_timestamps admitted properties d trace oldEntry retained
  have completed := cache_hit_completion shape commands key host cache incr
    related.incrAdmissible.operational d.selection d.selected hostD p i sb s memo head
    hit.sandbox hit.buffer hit.cacheable hit.entry historical witness validBase timestamps
    ∅ Set.finite_empty
  obtain ⟨closing, call, status, flag, output, patch, reads, writes, fresh, domains, bounds⟩ := completed.1
  have outputEq : closing.output = ⟨hit.tail, .eof⟩ := by
    have equality := output.symm.trans hit.guard
    have bytes := congrArg Chunk.bytes equality
    have suffix : closing.output.bytes = hit.tail := List.append_cancel_left bytes
    cases he : closing.output with
    | mk bytes f => simp_all
  have staged : FMap.dom sb.patch ⊆ Q := by
    rw [← slice.1]
    exact old_writes_accesses incr.trace d _
  have allBounds : FMap.dom closing.reads ∪ FMap.dom closing.writes ⊆ Q := by
    intro q member
    rcases bounds member with dependency | written
    · exact dependencyBounds dependency
    · exact staged written
  have agreement := call_agreement slices (selected_overlay host related hostD chosen)
    i sb hit.sandbox entry init current Q excluded
  refine ⟨sb.view, closing, ?_, approx_restrict_subset agreement allBounds, ?_, ?_, ?_, ?_⟩
  · simpa only [head, Head.probe, input] using call
  · simpa only [result, Memo.result] using status
  · exact outputEq.trans produced.symm
  · intro k atComponent
    have same := Option.some.inj (position.symm.trans atComponent)
    subst k
    rw [result]
    exact accounting closing.patch memo.patch closing.reads memo.reads closing.writes memo.writes
      (patch_symm patch) reads.symm writes.symm
  · simp only [CallPatch, noCall, head]
    intro other found
    have same : other = sb := Option.some.inj (found.symm.trans hit.sandbox)
    subst other
    simpa only [result, Memo.result] using patch

/-- Standalone replay uses `lem:paper-cache-reuse` at the actual selected live
filesystem. -/
theorem standalone_hit_forward_witness (shape : DenotationShape m) (commands : WellFormedCommands m)
    (key : HashInjective m) (host : HostWellFormed m h)
    {witnesses : WitnessMap sig} {incr : Prefix m h .incr prog start}
    {vanilla : Prefix m h .vanilla prog start} (related : BisimRelated witnesses incr vanilla)
    (properties : BisimPrefixProperties witnesses incr) (d : StepDerivation m h .incr prog)
    (before : d.before = incr.final)
    {sv : Selection sig} {wv : World sig} (chosen : h.select prog vanilla.final sv wv)
    {p : sig.Probe} {s : Bytes} {memo : Memo sig}
    (head : d.selection.head = .standalone p)
    (entry : FMap.get d.selected.cache (cacheKey m p d.selected.env ⟨s, .eof⟩) = some memo)
    (valid : Valid m memo.reads memo.writes d.selected.fs)
    (input : ProbeDerivation.input d.probe = ⟨s, .eof⟩)
    (result : ProbeDerivation.result d.probe = memo.result)
    (produced : ProbeDerivation.produced d.probe = memo.output) : ForwardWitness incr.trace d wv := by
  have hostD : h.select prog incr.final d.selection d.selected := before ▸ d.host
  have discipline := host.selectionDiscipline _ _ _ incr related.incrAdmissible.operational _ _ hostD
  obtain ⟨fs, witness, timestamps⟩ :=
    selected_cache_witnesses host incr related.incrAdmissible properties hostD _ memo entry
  have cache : WellFormedCache m d.selected.cache := discipline.2.2.1 ▸ related.cache
  have reused := validation_and_cache_reuse shape commands key _ cache p d.selected.env
    ⟨s, .eof⟩ memo fs d.selected.fs rfl entry witness valid timestamps
  refine ⟨d.selected.fs, memo.result, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [head, Head.probe, input] using reused.2.1
  · exact approx_restrict (standalone_selected_agreement host related hostD chosen head) _
  · rw [result]
  · exact produced.symm
  · apply call_paths_domains <;> rw [result]
  · unfold CallPatch
    split
    · rename_i impossible
      simp_all
    · rw [result]
      exact ⟨rfl, fun _ _ => rfl⟩

/-- Every actual forward source edge supplies a denoted remaining call, including
both hit constructors, with no extra call or validation premise. -/
theorem forward_witness (shape : DenotationShape m) (commands : WellFormedCommands m)
    (key : HashInjective m) (host : HostWellFormed m h) (cache : WellFormedCache m start.cache)
    {witnesses : WitnessMap sig} {incr full : Prefix m h .incr prog start}
    {vanilla : Prefix m h .vanilla prog start} (related : BisimRelated witnesses incr vanilla)
    (properties : BisimPrefixProperties witnesses incr) (admitted : Admissible witnesses full)
    (d : StepDerivation m h .incr prog) (hbefore : d.before = incr.final)
    (trace : full.trace = incr.trace ++ [d])
    {sv : Selection sig} {wv : World sig} (target : h.select prog vanilla.final sv wv) :
    ForwardWitness incr.trace d wv := by
  have isolated : Isolated (incr.trace ++ [d]) := trace ▸ admitted.isolated
  rcases d with ⟨before, ⟨head, initialization, delivery⟩, selected, after, out, chosen, derivation⟩
  cases derivation with
  | pipelineOpen p i sb taken remaining r buffers out hb hs hi ho call status flag route =>
    exact executing_forward_witness host related properties _ hbefore isolated target sb.view rfl
  | uncacheClose p i sb s r es buffers out hc hb hs call status flag route =>
    exact executing_forward_witness host related properties _ hbefore isolated target sb.view rfl
  | cacheCloseMiss p i sb s r es buffers out hc hb hs hi ho miss call status flag route =>
    exact executing_forward_witness host related properties _ hbefore isolated target sb.view rfl
  | cacheCloseHit p i sb s tail memo buffers out hc hb hs hi ho entry valid guard route =>
    exact pipeline_hit_forward_witness shape commands key host cache related properties admitted
      _ hbefore trace target rfl ⟨tail, buffers, out, hi, ho, hc, hb, hs, entry,
        (useCache_iff_of_get entry).mp valid, guard, route⟩
      rfl rfl rfl rfl
  | uncacheStandalone p s r es hc stdin call status =>
    exact executing_forward_witness host related properties _ hbefore isolated target selected.fs rfl
  | cacheStandaloneMiss p s r es hc stdin miss call status flag =>
    exact executing_forward_witness host related properties _ hbefore isolated target selected.fs rfl
  | cacheStandaloneHit p s memo hc stdin entry valid flag =>
    exact standalone_hit_forward_witness shape commands key host related properties _ hbefore
      target rfl entry valid rfl rfl rfl

theorem forward_probe_canonical {w v after : World sig} {head : Head sig} {out : Option Chunk}
    (d : IncrDerivation m w head after out) (control : ControlAgree w v) (r : Result sig)
    (call : m.denotes head.probe (IncrDerivation.input d) v.fs v.env r)
    (status : r.status = (IncrDerivation.result d).status)
    (output : r.output = IncrDerivation.produced d) :
    ∃ vafter, ∃ vd : VanillaDerivation m v head vafter out,
      ControlAgree after vafter ∧ VanillaDerivation.input vd = IncrDerivation.input d ∧
      VanillaDerivation.result vd = r := by
  cases head <;> exact forward_probe d control r call status output

theorem vanilla_result_cast {w after : World sig} {head head' : Head sig}
    {out : Option Chunk} (eq : head = head') (d : VanillaDerivation m w head after out) :
    VanillaDerivation.result (eq ▸ d) = VanillaDerivation.result d := by
  cases eq
  rfl

/-- Fresh target calls and concrete vanilla derivations for every actual forward edge. -/
theorem forward_raw_pair (shape : DenotationShape m) (commands : WellFormedCommands m)
    (key : HashInjective m) (host : HostWellFormed m h) (cache : WellFormedCache m start.cache)
    {witnesses : WitnessMap sig} {incr full : Prefix m h .incr prog start}
    {vanilla : Prefix m h .vanilla prog start} (related : BisimRelated witnesses incr vanilla)
    (properties : BisimPrefixProperties witnesses incr) (admitted : Admissible witnesses full)
    (d : StepDerivation m h .incr prog) (before : d.before = incr.final)
    (trace : full.trace = incr.trace ++ [d]) :
    ∃ dv : StepDerivation m h .vanilla prog, dv.before = vanilla.final ∧ PaperStepsMatch d dv ∧
      CallPaths incr.trace d (ProbeDerivation.result dv.probe) ∧
      CallPatch d (ProbeDerivation.result dv.probe) ∧ ProbeDerivation.Fresh dv.probe ∧
      (∀ q file, FMap.get (ProbeDerivation.result dv.probe).patch q = some (.write file) →
        ∀ q' old, (q', old) ∈ vanilla.records ++ witnessRecords witnesses → file.mtime ≠ old.mtime) := by
  obtain ⟨sv, wv, chosen, matching, control⟩ :=
    forward_selection host related d.selection d.selected (before ▸ d.host)
  obtain ⟨fs, r, call, agreement, status, output, paths, patch⟩ :=
    forward_witness shape commands key host cache related properties admitted d before trace chosen
  obtain ⟨r', call', status', output', writes', reads', patch', fresh, recordFresh⟩ :=
    transport_fresh commands call agreement (vanilla.records ++ witnessRecords witnesses)
      (live := wv.fs)
  have callTarget : m.denotes d.selection.head.probe (ProbeDerivation.input d.probe) wv.fs wv.env r' := by
    simpa only [control.2.2.1] using call'
  obtain ⟨after, vd, afterControl, inputEq, resultEq⟩ := forward_probe_canonical d.probe control r'
    callTarget (status'.trans status) (output'.trans output)
  let dv : StepDerivation m h .vanilla prog :=
    ⟨vanilla.final, sv, wv, after, d.out, chosen, matching.1 ▸ vd⟩
  have resultDv : ProbeDerivation.result dv.probe = r' := by
    exact (vanilla_result_cast matching.1 vd).trans resultEq
  refine ⟨dv, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨rfl, control, afterControl, matching.1, matching.2.1⟩
  · rw [resultDv]
    exact call_paths_transport paths patch' reads' writes'
  · rw [resultDv]
    exact call_patch_transport patch patch'
  · unfold ProbeDerivation.Fresh
    simp only [ProbeDerivation.callFS, VanillaDerivation.callFS, resultDv]
    exact fresh
  · rw [resultDv]
    exact recordFresh

/-- Matched trace positions and selections identify the same new invocation. -/
theorem paired_new_component {left : Trace m h .incr prog} {right : Trace m h .vanilla prog}
    (paired : List.Forall₂ PaperStepsMatch left right)
    {di : StepDerivation m h .incr prog} {dv : StepDerivation m h .vanilla prog}
    (matched : PaperStepsMatch di dv) :
    componentAt (left ++ [di]) left.length di = componentAt (right ++ [dv]) right.length dv := by
  have lengthEq := paired.length_eq
  have heads := matched.2.2.2.1
  have inits := matched.2.2.2.2
  rw [componentAt_snoc_last, componentAt_snoc_last]
  have alternatives : (∃ p, di.selection.head = .standalone p) ∨
      (∃ p i, di.selection.head = .pipeline p i) := by
    cases di.selection.head
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inr ⟨_, _, rfl⟩
  rcases alternatives with ⟨p, head⟩ | ⟨p, i, head⟩
  · rw [← heads, head, lengthEq]
  · rw [← heads, head]
    cases hi : di.selection.init <;> cases hv : dv.selection.init <;>
      simp only [hi, hv, Option.map_none, Option.map_some, reduceCtorEq] at inits
    · simpa only [selectedComponent, selectedPipeline, liveComponent, hi, hv] using live_components paired i
    · simp only [selectedComponent, selectedPipeline, hi, hv, Option.map_some, lengthEq]

/-- One new record adds precisely its selected result's write paths. -/
theorem writes_snoc {executor : Executor} (trace : Trace m h executor prog)
    (d : StepDerivation m h executor prog) (k : Component) :
    componentWrites (trace ++ [d]) k = componentWrites trace k ∪
      (if componentAt (trace ++ [d]) trace.length d = some k then
        FMap.dom (ProbeDerivation.result d.probe).patch else ∅) := by
  classical
  ext q
  simp only [componentWrites, componentSteps_snoc, List.mem_append, Set.mem_union]
  split_ifs <;> simp_all

/-- One new record adds precisely its effect and dependency paths. -/
theorem accesses_snoc {executor : Executor} (trace : Trace m h executor prog)
    (d : StepDerivation m h executor prog) (k : Component) :
    componentAccesses (trace ++ [d]) k = componentAccesses trace k ∪
      (if componentAt (trace ++ [d]) trace.length d = some k then
        FMap.dom (ProbeDerivation.result d.probe).patch ∪
          FMap.dom (ProbeDerivation.result d.probe).reads ∪
          FMap.dom (ProbeDerivation.result d.probe).writes else ∅) := by
  classical
  ext q
  simp only [componentAccesses, componentDeps, componentWrites, componentSteps_snoc,
    List.mem_append, Set.mem_union]
  split_ifs <;> simp_all
  aesop

/-- `lem:paper-bisim-prefix` hit accounting and transported domains preserve every
cumulative path set. -/
theorem paths_snoc {left : Trace m h .incr prog} {right : Trace m h .vanilla prog}
    (paired : List.Forall₂ PaperStepsMatch left right) (paths : PathSetsAgree left right)
    {di : StepDerivation m h .incr prog} {dv : StepDerivation m h .vanilla prog}
    (matched : PaperStepsMatch di dv) (accounting : CallPaths left di (ProbeDerivation.result dv.probe)) :
    PathSetsAgree (left ++ [di]) (right ++ [dv]) := by
  intro k
  rw [writes_snoc, writes_snoc, accesses_snoc, accesses_snoc, ← paired_new_component paired matched]
  by_cases component : componentAt (left ++ [di]) left.length di = some k
  · simp only [component, ite_true]
    rw [← (paths k).1, ← (paths k).2]
    obtain ⟨hw, ha⟩ := accounting k component
    refine ⟨hw, ?_⟩
    simpa only [Set.union_assoc] using ha
  · simp only [component, ite_false, Set.union_empty]
    exact paths k

/-- Matched selection annotations retain absolute entry positions before calls exist. -/
theorem selected_component_match {left : Trace m h .incr prog} {right : Trace m h .vanilla prog}
    (paired : List.Forall₂ PaperStepsMatch left right) {si sv : Selection sig}
    (inits : si.init.map (·.probes) = sv.init.map (·.probes)) (i : Nat) :
    selectedComponent left si i = selectedComponent right sv i := by
  cases hi : si.init <;> cases hv : sv.init <;>
    simp only [hi, hv, Option.map_none, Option.map_some, reduceCtorEq] at inits
  · simpa only [selectedComponent, selectedPipeline, liveComponent, hi, hv] using live_components paired i
  · simp only [selectedComponent, selectedPipeline, hi, hv, Option.map_some, paired.length_eq]

/-- The given vanilla successor excludes all older Incr other-component writes. -/
theorem backward_other_exclusion {incr : Trace m h .incr prog} {vanilla : Trace m h .vanilla prog}
    (paths : PathSetsAgree incr vanilla) (d : StepDerivation m h .vanilla prog)
    (isolated : Isolated (vanilla ++ [d])) (entry i : Nat) :
    Disjoint (componentAccesses (vanilla ++ [d]) (.pipeline entry i)) (otherWrites incr entry i) := by
  apply Set.disjoint_left.mpr
  intro q access written
  obtain ⟨j, distinct, member⟩ := PrefixProperties.mem_otherWrites.mp written
  rw [(paths (.pipeline entry j)).1] at member
  exact Set.disjoint_left.mp (source_exclusion vanilla d isolated entry i j distinct.symm) access member

/-- Every vanilla rule retains an actual live-filesystem denotation. -/
theorem vanilla_call {w after : World sig} {head : Head sig} {out : Option Chunk}
    (d : VanillaDerivation m w head after out) :
    m.denotes head.probe (VanillaDerivation.input d) w.fs w.env (VanillaDerivation.result d) := by
  cases d <;> assumption

/-- Backward pipeline transport uses the given vanilla edge's enlarged accesses. -/
theorem backward_pipeline_agreement (host : HostWellFormed m h)
    {witnesses : WitnessMap sig} {incr : Prefix m h .incr prog start}
    {vanilla : Prefix m h .vanilla prog start} (related : BisimRelated witnesses incr vanilla)
    (properties : BisimPrefixProperties witnesses incr) (d : StepDerivation m h .vanilla prog)
    (before : d.before = vanilla.final) (isolated : Isolated (vanilla.trace ++ [d]))
    {si : Selection sig} {wi : World sig} (chosen : h.select prog incr.final si wi)
    (matching : MatchingSelections d.selection si d.selected wi)
    {p : sig.Probe} {i : Nat} {sb : Sandbox sig}
    (head : d.selection.head = .pipeline p i) (sandbox : FMap.get wi.sandbox i = some sb) :
    ∃ entry init, selectedPipeline incr.trace si = some (entry, init) ∧
      FSApprox (d.selected.fs ↾ componentAccesses (vanilla.trace ++ [d]) (.pipeline entry i))
        (sb.view ↾ componentAccesses (vanilla.trace ++ [d]) (.pipeline entry i)) ∧
      componentAt (vanilla.trace ++ [d]) vanilla.trace.length d = some (.pipeline entry i) ∧
      sb.base ↾ componentAccesses (vanilla.trace ++ [d]) (.pipeline entry i) =
        wi.fs ↾ componentAccesses (vanilla.trace ++ [d]) (.pipeline entry i) := by
  have slices := properties.2.2 _ _ chosen
  obtain ⟨entry, init, current, slice, accounting⟩ := slices i sb sandbox
  have excluded := backward_other_exclusion related.paths d isolated entry i
  have agreement := call_agreement slices
    (selected_overlay host related chosen (before ▸ d.host)) i sb sandbox entry init current _ excluded
  refine ⟨entry, init, current, FSApprox.of_contents (fun q => (agreement.contents q).symm), ?_,
    slice.2.2 _ excluded⟩
  rw [componentAt_snoc_last, head]
  have component := selected_component_match related.steps matching.2.1.symm i
  simp only [selectedComponent, current, Option.map_some] at component
  exact component.symm

/-- Candidate remaining calls retain exact patch identity for later provenance checks. -/
structure BackwardCall (d : StepDerivation m h .vanilla prog) (si : Selection sig)
    (wi : World sig) (records : Records sig) where
  fs : FS sig
  result : Result sig
  location : CallLocation si.head wi fs
  call : m.denotes d.selection.head.probe (ProbeDerivation.input d.probe) fs wi.env result
  status : result.status = (ProbeDerivation.result d.probe).status
  output : result.output = (ProbeDerivation.result d.probe).output
  writes : result.writes = (ProbeDerivation.result d.probe).writes
  reads : FMap.dom result.reads = FMap.dom (ProbeDerivation.result d.probe).reads
  patch : PatchApprox result.patch (ProbeDerivation.result d.probe).patch
  fresh : FreshPatch result.patch fs wi.fs
  recordFresh : ∀ q file, FMap.get result.patch q = some (.write file) →
    ∀ q' old, (q', old) ∈ records → file.mtime ≠ old.mtime

/-- Backward transfer chooses a fresh concrete remaining call at the selected Incr filesystem. -/
theorem backward_call (commands : WellFormedCommands m) (host : HostWellFormed m h)
    {witnesses : WitnessMap sig} {incr : Prefix m h .incr prog start}
    {vanilla : Prefix m h .vanilla prog start} (related : BisimRelated witnesses incr vanilla)
    (properties : BisimPrefixProperties witnesses incr) (d : StepDerivation m h .vanilla prog)
    (before : d.before = vanilla.final) (isolated : Isolated (vanilla.trace ++ [d]))
    {si : Selection sig} {wi : World sig} (chosen : h.select prog incr.final si wi)
    (matching : MatchingSelections d.selection si d.selected wi)
    (control : ControlAgree d.selected wi) (records : Records sig) :
    Nonempty (BackwardCall d si wi records) := by
  have actual := vanilla_call d.probe
  have alternatives : (∃ p, d.selection.head = .standalone p) ∨
      (∃ p i, d.selection.head = .pipeline p i) := by
    cases d.selection.head
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inr ⟨_, _, rfl⟩
  rcases alternatives with ⟨p, head⟩ | ⟨p, i, head⟩
  · have headI : si.head = .standalone p := matching.1.symm.trans head
    have agreement := standalone_selected_agreement host related chosen (before ▸ d.host) headI
    have reverse := FSApprox.of_contents (fun q => (agreement.contents q).symm)
    obtain ⟨r, call, status, output, writes, reads, patch, fresh, recordFresh⟩ :=
      transport_fresh commands actual (approx_restrict reverse _) records (live := wi.fs)
    refine ⟨⟨wi.fs, r, ?_, ?_, status, output, writes, reads, patch, fresh, recordFresh⟩⟩
    · simp only [CallLocation, headI]
    · simpa only [control.2.2.1, ProbeDerivation.input] using call
  · have headI : si.head = .pipeline p i := matching.1.symm.trans head
    have discipline := host.selectionDiscipline _ _ _ incr related.incrAdmissible.operational _ _ chosen
    have hasSandbox := discipline.2.2.2.2
    rw [headI] at hasSandbox
    obtain ⟨sb, sandbox⟩ := Finmap.mem_iff.mp (Finmap.mem_keys.mp hasSandbox.2.2.1)
    obtain ⟨entry, init, current, agreement, position, base⟩ :=
      backward_pipeline_agreement host related properties d before isolated chosen matching head sandbox
    obtain ⟨r, call, status, output, writes, reads, patch, fresh, recordFresh⟩ :=
      transport_fresh commands actual
        (approx_restrict_subset agreement (snoc_dependencies vanilla.trace d position)) records (live := wi.fs)
    refine ⟨⟨sb.view, r, ?_, ?_, status, output, writes, reads, patch, fresh, recordFresh⟩⟩
    · simp only [CallLocation, headI]
      exact ⟨sb, sandbox, rfl⟩
    · simpa only [control.2.2.1, ProbeDerivation.input] using call

/-- Older accesses remain accesses after one appended record. -/
theorem old_accesses_subset {executor : Executor} (trace : Trace m h executor prog)
    (d : StepDerivation m h executor prog) (k : Component) :
    componentAccesses trace k ⊆ componentAccesses (trace ++ [d]) k := by
  intro q member
  rcases member with ⟨old, member, path⟩ | ⟨old, member, path⟩
  · exact Or.inl ⟨old, C9.componentSteps_append_subset trace [d] k old member, path⟩
  · exact Or.inr ⟨old, C9.componentSteps_append_subset trace [d] k old member, path⟩

/-- Exact dependency agreement supplies the cacheable command's exact result,
not only a result with equivalent timestamps. -/
theorem cacheable_exact_transport (commands : WellFormedCommands m) {p : sig.Probe}
    (cacheable : Cacheable m p) {input : Chunk} {fs target : FS sig} {env : Env sig}
    {r : Result sig} (call : m.denotes p input fs env r)
    (agree : DepAgree r.reads r.writes fs target) : m.denotes p input target env r := by
  obtain ⟨⟨other, denoted⟩, equivalent⟩ := cacheable input fs env r call target agree
  have comparison := equivalent other denoted
  have retimed := commands.timestamps.retimestamp p input target env other denoted r.patch
    (patch_symm comparison.2)
  have equality : {other with patch := r.patch} = r := by
    have fields := comparison.1
    cases other
    cases r
    simp_all only [Prod.mk.injEq]
  exact equality ▸ retimed

/-- `lem:paper-sandbox` folds the actual selected candidate. Source vanilla
isolation and `lem:paper-bisim-prefix` transport the complete folded result from
its base to the live filesystem. -/
theorem backward_folded (_shape : DenotationShape m) (commands : WellFormedCommands m)
    (_key : HashInjective m) (host : HostWellFormed m h)
    {witnesses : WitnessMap sig} {incr : Prefix m h .incr prog start}
    {vanilla : Prefix m h .vanilla prog start} (related : BisimRelated witnesses incr vanilla)
    (properties : BisimPrefixProperties witnesses incr) (d : StepDerivation m h .vanilla prog)
    (before : d.before = vanilla.final) (isolated : Isolated (vanilla.trace ++ [d]))
    {si : Selection sig} {wi : World sig} (chosen : h.select prog incr.final si wi)
    (matching : MatchingSelections d.selection si d.selected wi)
    {p : sig.Probe} {i : Nat} {sb : Sandbox sig} {s : Bytes} {r : Result sig}
    (head : d.selection.head = .pipeline p i) (sandbox : FMap.get wi.sandbox i = some sb)
    (_input : ProbeDerivation.input d.probe = ⟨s, .eof⟩) (cacheable : Cacheable m p)
    (call : m.denotes p ⟨s, .eof⟩ sb.view wi.env r)
    (reads : FMap.dom r.reads = FMap.dom (ProbeDerivation.result d.probe).reads)
    (writes : r.writes = (ProbeDerivation.result d.probe).writes)
    (hi : sb.input.flag = .open) (ho : sb.output.flag = .open) :
    m.denotes p (sb.input++'hi⟨s, .eof⟩) wi.fs wi.env (combineResults (sandboxResult sb) r ho) := by
  classical
  have headI : si.head = .pipeline p i := matching.1.symm.trans head
  have state := related.incrSandboxes
  have prefixes := related.incrPrefixes
  have cases := hit_selected_prefix_cases related.incrAdmissible.operational host state prefixes
    chosen headI sandbox cacheable
  have folded : m.denotes p (sb.input++'hi⟨s, .eof⟩) sb.base wi.env
      (combineResults (sandboxResult sb) r ho) := by
    rcases cases with initial | previous
    · have call' : m.denotes p ⟨s, .eof⟩ (Sandbox.initial sb.base).view wi.env r := by
        simpa only [← initial] using call
      convert CachePrefixes.fold_initial call' using 1 <;> simp only [← initial]
    · exact CachePrefixes.fold_progressed commands cacheable hi ho previous call
  obtain ⟨entry, init, current, agreement, position, baseEq⟩ :=
    backward_pipeline_agreement host related properties d before isolated chosen matching head sandbox
  obtain ⟨entry', init', current', slice, accounting⟩ := (properties.2.2 _ _ chosen) i sb sandbox
  have entries := Option.some.inj (current.symm.trans current')
  cases entries
  let Q := componentAccesses (vanilla.trace ++ [d]) (.pipeline entry i)
  have candidate : FMap.dom r.reads ∪ FMap.dom r.writes ⊆ Q := by
    rw [reads, writes]
    exact snoc_dependencies vanilla.trace d position
  have earlier : FMap.dom sb.reads ∪ FMap.dom sb.writes ⊆ Q := by
    intro q member
    have oldAccess : q ∈ componentAccesses incr.trace (.pipeline entry i) := by
      rw [slice.2.1]
      rcases member with read | write
      · exact Or.inl (Or.inr read)
      · exact Or.inr write
    rw [(related.paths (.pipeline entry i)).2] at oldAccess
    exact old_accesses_subset vanilla.trace d _ oldAccess
  have bounds : FMap.dom (combineResults (sandboxResult sb) r ho).reads ∪
      FMap.dom (combineResults (sandboxResult sb) r ho).writes ⊆ Q := by
    intro q member
    simp only [combineResults, sandboxResult, FMap.dom_merge] at member
    rcases member with (read | nextRead) | (write | nextWrite)
    · exact earlier (Or.inl read)
    · exact candidate (Or.inl (FMap.filterKeys_dom_subset _ _ nextRead))
    · exact earlier (Or.inr write)
    · exact candidate (Or.inr (FMap.filterKeys_dom_subset _ _ nextWrite))
  have valid := commands.dependencies.valid _ _ _ _ _ folded
  have targetValid := valid_of_restrict valid baseEq bounds
  have get q (member : q ∈ FMap.dom (combineResults (sandboxResult sb) r ho).reads ∪
      FMap.dom (combineResults (sandboxResult sb) r ho).writes) :
      FMap.get sb.base q = FMap.get wi.fs q := by
    have equality := congrArg (fun fs => FMap.get fs q) baseEq
    have covered : q ∈ componentAccesses (vanilla.trace ++ [d]) (.pipeline entry i) := bounds member
    simpa [FMap.get_restrict, covered] using equality
  apply cacheable_exact_transport commands cacheable folded
  refine ⟨fun q member => ⟨valid.1 member, targetValid.1 member⟩,
    fun q read => get q (Or.inl read), fun q write => ?_⟩
  rw [get q (Or.inr write)]

theorem equivalent_symm {r r' : Result sig} (eq : ResultEquivalent r r') : ResultEquivalent r' r :=
  ⟨eq.1.symm, patch_symm eq.2⟩

/-- Standalone dispatch retains exact executing-result identity or identifies a replay.
This distinction certifies timestamps without treating patch approximation as equality. -/
theorem choose_standalone (shape : DenotationShape m) (commands : WellFormedCommands m)
    (key : HashInjective m) {w v : World sig} (control : ControlAgree w v)
    (cache : WellFormedCache m w.cache)
    (witnesses : ∀ k memo, FMap.get w.cache k = some memo →
      ∃ fs, EntryWitness m k memo fs ∧ TimestampConsistent ({recordOfFS fs} ∪ {recordOfFS w.fs}))
    (p : sig.Probe) (s : Bytes) (r : Result sig) (es : Nat)
    (stdin : v.stdin = ⟨s, .eof⟩) (call : m.denotes p ⟨s, .eof⟩ w.fs w.env r)
    (status : r.status = some es) :
    ∃ after out, ∃ d : IncrDerivation m w (.standalone p) after out,
      ControlAgree after (standaloneWorld v es r.patch) ∧ out = some r.output ∧
      IncrDerivation.input d = ⟨s, .eof⟩ ∧ IncrDerivation.produced d = r.output ∧
      (IncrDerivation.result d = r ∨ (IncrDerivation.callFS d = none ∧
        ResultEquivalent r (IncrDerivation.result d))) := by
  classical
  obtain ⟨pc, oldStatus, env, buffersEq, stdinEq⟩ := control
  have stdin' := stdinEq.trans stdin
  have flag := (shape _ _ _ _ _ call).2 rfl |>.1
  by_cases cacheable : Cacheable m p
  · cases found : FMap.get w.cache (cacheKey m p w.env ⟨s, .eof⟩) with
    | none =>
      refine ⟨_, _, .cacheStandaloneMiss w p s r es cacheable stdin' (Or.inl found) call status flag, ?_⟩
      exact ⟨⟨pc, rfl, env, buffersEq, rfl⟩, rfl, rfl, rfl, Or.inl rfl⟩
    | some memo =>
      by_cases valid : Valid m memo.reads memo.writes w.fs
      · obtain ⟨fs, witness, timestamps⟩ := witnesses _ memo found
        have reused := validation_and_cache_reuse shape commands key w.cache cache
          p w.env ⟨s, .eof⟩ memo fs w.fs rfl found witness valid timestamps
        have comparison := reused.2.2 r call
        have fields := comparison.1
        simp only [Prod.mk.injEq, Memo.result] at fields
        have sameStatus : memo.ec = es := Option.some.inj (fields.1.symm.trans status)
        refine ⟨_, _, .cacheStandaloneHit w p s memo cacheable stdin' found valid memo.output_eof, ?_⟩
        exact ⟨⟨pc, sameStatus, env, buffersEq, rfl⟩, congrArg some fields.2.2.2.symm,
          rfl, fields.2.2.2.symm, Or.inr ⟨rfl, equivalent_symm comparison⟩⟩
      · refine ⟨_, _, .cacheStandaloneMiss w p s r es cacheable stdin'
          (Or.inr ⟨memo, found, valid⟩) call status flag, ?_⟩
        exact ⟨⟨pc, rfl, env, buffersEq, rfl⟩, rfl, rfl, rfl, Or.inl rfl⟩
  · refine ⟨_, _, .uncacheStandalone w p s r es cacheable stdin' call status, ?_⟩
    exact ⟨⟨pc, rfl, env, buffersEq, rfl⟩, rfl, rfl, rfl, Or.inl rfl⟩

/-- Cacheable closing dispatch retains the folded comparison and exact candidate
identity on executed misses. It proves the hit guard from the live denotation. -/
theorem choose_cache_close (shape : DenotationShape m) (commands : WellFormedCommands m)
    (key : HashInjective m) {w v : World sig} (control : ControlAgree w v)
    (cache : WellFormedCache m w.cache)
    (witnesses : ∀ k memo, FMap.get w.cache k = some memo →
      ∃ fs, EntryWitness m k memo fs ∧ TimestampConsistent ({recordOfFS fs} ∪ {recordOfFS w.fs}))
    (p : sig.Probe) (i : Nat) (sb : Sandbox sig) (s : Bytes) (r : Result sig)
    (es : Nat) (buffers : FMap Nat Chunk) (out : Option Chunk)
    (cacheable : Cacheable m p) (sandbox : FMap.get w.sandbox i = some sb)
    (hi : sb.input.flag = .open) (ho : sb.output.flag = .open)
    (buffer : FMap.get v.buffer i = some ⟨s, .eof⟩)
    (call : m.denotes p ⟨s, .eof⟩ sb.view w.env r)
    (status : r.status = some es) (flag : r.output.flag = .eof)
    (route : put (v.buffer ∖ i) i r.output = some (buffers, out))
    (whole : m.denotes p (sb.input++'hi⟨s, .eof⟩) w.fs w.env (combineResults (sandboxResult sb) r ho)) :
    ∃ after, ∃ d : IncrDerivation m w (.pipeline p i) after out,
      ControlAgree after (closeWorld v i es r.patch buffers) ∧
      IncrDerivation.input d = ⟨s, .eof⟩ ∧ IncrDerivation.produced d = r.output ∧
      ((IncrDerivation.result d = r ∧ IncrDerivation.callFS d = some sb.view) ∨
        (IncrDerivation.callFS d = none ∧
        ResultEquivalent (combineResults (sandboxResult sb) r ho) (IncrDerivation.result d))) := by
  classical
  obtain ⟨pc, oldStatus, env, buffersEq, stdinEq⟩ := control
  have buffer' : FMap.get w.buffer i = some ⟨s, .eof⟩ := by simpa only [buffersEq] using buffer
  have route' : put (w.buffer ∖ i) i r.output = some (buffers, out) := by
    simpa only [buffersEq] using route
  cases found : FMap.get w.cache (cacheKey m p w.env (sb.input ++'hi ⟨s, .eof⟩)) with
  | none =>
    refine ⟨_, .cacheCloseMiss w p i sb s r es buffers out cacheable buffer' sandbox hi ho
      ((cacheMiss_iff_not_useCache m w _).mp (Or.inl found)) call status flag route', ?_⟩
    exact ⟨⟨pc, rfl, env, rfl, stdinEq⟩, rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩
  | some memo =>
    by_cases valid : Valid m memo.reads memo.writes w.fs
    · obtain ⟨fs, witness, timestamps⟩ := witnesses _ memo found
      have reused := validation_and_cache_reuse shape commands key w.cache cache
        p w.env (sb.input ++'hi ⟨s, .eof⟩) memo fs w.fs rfl found witness valid timestamps
      have comparison := reused.2.2 _ whole
      have fields := comparison.1
      simp only [Prod.mk.injEq, combineResults, sandboxResult, Memo.result] at fields
      have sameStatus : memo.ec = es := Option.some.inj (fields.1.symm.trans status)
      have outputEq : r.output = ⟨r.output.bytes, .eof⟩ := by
        cases he : r.output with | mk bytes f => simp_all
      have guard : memo.output = sb.output ++'ho ⟨r.output.bytes, .eof⟩ := by
        rw [← outputEq]
        exact fields.2.2.2.symm
      refine ⟨_, .cacheCloseHit w p i sb s r.output.bytes memo buffers out cacheable
        buffer' sandbox hi ho found ((useCache_iff_of_get found).mpr valid) guard (by rw [← outputEq]; exact route'), ?_⟩
      exact ⟨⟨pc, sameStatus, env, rfl, stdinEq⟩, rfl, outputEq.symm,
        Or.inr ⟨rfl, equivalent_symm comparison⟩⟩
    · refine ⟨_, .cacheCloseMiss w p i sb s r es buffers out cacheable buffer' sandbox hi ho
        ((cacheMiss_iff_not_useCache m w _).mp (Or.inr ⟨memo, found, valid⟩)) call status flag route', ?_⟩
      exact ⟨⟨pc, rfl, env, rfl, stdinEq⟩, rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩

theorem call_location_unique {head : Head sig} {w : World sig} {fs target : FS sig}
    (left : CallLocation head w fs) (right : CallLocation head w target) : fs = target := by
  cases head with
  | standalone p => exact left.trans right.symm
  | pipeline p i =>
    obtain ⟨sb, found, rfl⟩ := left
    obtain ⟨other, found', rfl⟩ := right
    have same := Option.some.inj (found.symm.trans found')
    cases same
    rfl

/-- Actual replay patches originate in the selected cache, with exact timestamps. -/
theorem replay_patch_sources {w after : World sig} {head : Head sig} {out : Option Chunk}
    (d : IncrDerivation m w head after out) (replay : IncrDerivation.callFS d = none)
    {record : sig.Path × File sig} (member : record ∈ patchRecords (IncrDerivation.result d).patch) :
    record ∈ cacheRecords w.cache := by
  cases d <;> simp only [IncrDerivation.callFS] at replay
  all_goals first
    | contradiction
    | (apply RecordInventory.cache_patch_sources (by assumption)
       exact member)

/-- Exact candidate identity certifies executions. Replays allocate no timestamps. -/
theorem choice_fresh {w after : World sig} {head : Head sig} {out : Option Chunk}
    (d : IncrDerivation m w head after out) (r : Result sig) (fs : FS sig)
    (location : CallLocation head w fs) (fresh : FreshPatch r.patch fs w.fs)
    (choice : IncrDerivation.result d = r ∨ IncrDerivation.callFS d = none) :
    ProbeDerivation.Fresh (executor := .incr) d := by
  unfold ProbeDerivation.Fresh
  simp only [ProbeDerivation.callFS, ProbeDerivation.result]
  cases executes : IncrDerivation.callFS d with
  | none => trivial
  | some actual =>
    have same := call_location_unique (incr_executing d actual executes).2.2 location
    rcases choice with identical | replay
    · rw [identical, same]
      exact fresh
    · rw [replay] at executes
      contradiction

/-- Candidate or selected-cache provenance accounts for every actual result patch. -/
theorem choice_sources {w after : World sig} {head : Head sig} {out : Option Chunk}
    (d : IncrDerivation m w head after out) (r : Result sig)
    (choice : IncrDerivation.result d = r ∨ IncrDerivation.callFS d = none)
    {record : sig.Path × File sig} (member : record ∈ patchRecords (IncrDerivation.result d).patch) :
    record ∈ cacheRecords w.cache ++ patchRecords r.patch := by
  rcases choice with identical | replay
  · exact List.mem_append_right _ (by simpa only [identical] using member)
  · exact List.mem_append_left _ (replay_patch_sources d replay member)

/-- Selected standalone choices give direct path and effect correspondence. -/
theorem standalone_choice {trace : Trace m h .incr prog} {d : StepDerivation m h .incr prog}
    {p : sig.Probe} (head : d.selection.head = .standalone p) {r : Result sig}
    (choice : ProbeDerivation.result d.probe = r ∨
      (ProbeDerivation.callFS d.probe = none ∧ ResultEquivalent r (ProbeDerivation.result d.probe))) :
    CallPaths trace d r ∧ CallPatch d r := by
  have equivalent : ResultEquivalent r (ProbeDerivation.result d.probe) := by
    rcases choice with identical | replay
    · rw [identical]
      exact ⟨rfl, ⟨rfl, fun _ _ => rfl⟩⟩
    · exact replay.2
  have fields := equivalent.1
  simp only [Prod.mk.injEq] at fields
  refine ⟨call_paths_domains trace d r equivalent.2.1 (congrArg FMap.dom fields.2.1)
    (congrArg FMap.dom fields.2.2.1), ?_⟩
  unfold CallPatch
  split
  · rename_i impossible
    simp_all
  · exact patch_symm equivalent.2

theorem filter_not_patch {V : Type} (map : FMap sig.Path V) (patch : Patch sig) :
    FMap.filterKeys (fun q => q ∉ FMap.keys patch) map = map ↾ (Set.univ \ FMap.dom patch) := by
  classical
  have predicate : (fun q => q ∉ FMap.keys patch) =
      (fun q => q ∈ (Set.univ \ FMap.dom patch)) := by
    funext q
    apply propext
    simp only [Set.mem_sdiff, Set.mem_univ, true_and, FMap.dom, FMap.keys, Set.mem_ofPred_eq]
  unfold FMap.restrict
  simp only [predicate]
  apply Finmap.ext_lookup
  intro q
  change FMap.get _ q = FMap.get _ q
  simp only [FMap.get_filterKeys]
  split_ifs <;> rfl

/-- Complete folded comparison and `lem:paper-bisim-prefix` hit accounting give
cumulative pipeline paths. -/
theorem pipeline_choice {trace : Trace m h .incr prog} {d : StepDerivation m h .incr prog}
    {p : sig.Probe} {i : Nat} {sb : Sandbox sig} {entry : Nat} {r : Result sig}
    (head : d.selection.head = .pipeline p i) (sandbox : FMap.get d.selected.sandbox i = some sb)
    (ho : sb.output.flag = .open)
    (position : componentAt (trace ++ [d]) trace.length d = some (.pipeline entry i))
    (accounting : HitPathAccounting trace (.pipeline entry i) sb)
    (choice : (ProbeDerivation.result d.probe = r ∧ ProbeDerivation.callFS d.probe = some sb.view) ∨
      (ProbeDerivation.callFS d.probe = none ∧
        ResultEquivalent (combineResults (sandboxResult sb) r ho) (ProbeDerivation.result d.probe))) :
    CallPaths trace d r ∧ CallPatch d r := by
  classical
  rcases choice with ⟨identical, executes⟩ | ⟨replay, equivalent⟩
  · refine ⟨call_paths_domains trace d r (by rw [identical]) (by rw [identical]) (by rw [identical]), ?_⟩
    simp only [CallPatch, executes, identical]
    exact ⟨rfl, fun _ _ => rfl⟩
  · have fields := equivalent.1
    simp only [Prod.mk.injEq, combineResults, sandboxResult] at fields
    refine ⟨?_, ?_⟩
    · intro k atComponent
      have same := Option.some.inj (position.symm.trans atComponent)
      subst k
      apply accounting r.patch (ProbeDerivation.result d.probe).patch r.reads
        (ProbeDerivation.result d.probe).reads r.writes (ProbeDerivation.result d.probe).writes equivalent.2
      · rw [← filter_not_patch]
        exact fields.2.1
      · rw [← filter_not_patch]
        exact fields.2.2.1
    · simp only [CallPatch, replay, head]
      intro other found
      have same := Option.some.inj (sandbox.symm.trans found)
      cases same
      exact patch_symm equivalent.2

def castIncr {w after : World sig} {head head' : Head sig} {out : Option Chunk}
    (eq : head = head') (d : IncrDerivation m w head after out) : IncrDerivation m w head' after out :=
  eq ▸ d

@[simp] theorem incr_result_cast {w after : World sig} {head head' : Head sig}
    {out : Option Chunk} (eq : head = head') (d : IncrDerivation m w head after out) :
    IncrDerivation.result (castIncr eq d) = IncrDerivation.result d := by cases eq; rfl

@[simp] theorem incr_callFS_cast {w after : World sig} {head head' : Head sig}
    {out : Option Chunk} (eq : head = head') (d : IncrDerivation m w head after out) :
    IncrDerivation.callFS (castIncr eq d) = IncrDerivation.callFS d := by cases eq; rfl

@[simp] theorem incr_input_cast {w after : World sig} {head head' : Head sig}
    {out : Option Chunk} (eq : head = head') (d : IncrDerivation m w head after out) :
    IncrDerivation.input (castIncr eq d) = IncrDerivation.input d := by cases eq; rfl

@[simp] theorem incr_produced_cast {w after : World sig} {head head' : Head sig}
    {out : Option Chunk} (eq : head = head') (d : IncrDerivation m w head after out) :
    IncrDerivation.produced (castIncr eq d) = IncrDerivation.produced d := by cases eq; rfl

theorem control_symm {a b : World sig} (eq : ControlAgree a b) : ControlAgree b a :=
  ⟨eq.1.symm, eq.2.1.symm, eq.2.2.1.symm, eq.2.2.2.1.symm, eq.2.2.2.2.symm⟩

/-- Pack a concrete backward dispatcher choice with its exact timestamp provenance. -/
theorem backward_pack (host : HostWellFormed m h)
    {witnesses : WitnessMap sig} {incr : Prefix m h .incr prog start}
    {vanilla : Prefix m h .vanilla prog start} (related : BisimRelated witnesses incr vanilla)
    (dv : StepDerivation m h .vanilla prog) (di : StepDerivation m h .incr prog)
    (before : di.before = incr.final) (_matched : PaperStepsMatch di dv)
    (candidate : BackwardCall dv di.selection di.selected (incr.records ++ witnessRecords witnesses))
    (choice : ProbeDerivation.result di.probe = candidate.result ∨ ProbeDerivation.callFS di.probe = none)
    (paths : CallPaths incr.trace di candidate.result) (patch : CallPatch di candidate.result) :
    ∃ newPatch : Patch sig, CallPaths incr.trace di (ProbeDerivation.result dv.probe) ∧
      CallPatch di (ProbeDerivation.result dv.probe) ∧ ProbeDerivation.Fresh di.probe ∧
      (∀ q file, FMap.get newPatch q = some (.write file) →
        ∀ q' old, (q', old) ∈ incr.records ++ witnessRecords witnesses → file.mtime ≠ old.mtime) ∧
      (∀ record ∈ patchRecords (ProbeDerivation.result di.probe).patch,
        record ∈ (incr.records ++ witnessRecords witnesses) ++ patchRecords newPatch) := by
  refine ⟨candidate.result.patch, call_paths_transport paths (patch_symm candidate.patch)
    candidate.reads.symm candidate.writes.symm,
    call_patch_transport patch (patch_symm candidate.patch),
    choice_fresh di.probe candidate.result candidate.fs candidate.location candidate.fresh choice,
    candidate.recordFresh, ?_⟩
  intro record member
  rcases List.mem_append.mp (choice_sources di.probe candidate.result choice member) with cached | generated
  · apply List.mem_append_left
    apply List.mem_append_left
    apply RecordInventory.selected_records host incr related.incrAdmissible.operational (before ▸ di.host)
    simp only [worldRecords, List.mem_append]
    exact Or.inl (Or.inr cached)
  · exact List.mem_append_right _ generated

def BackwardRawPair (witnesses : WitnessMap sig) (incr : Prefix m h .incr prog start)
    (dv : StepDerivation m h .vanilla prog) : Prop :=
  ∃ di : StepDerivation m h .incr prog, ∃ newPatch : Patch sig,
    di.before = incr.final ∧ PaperStepsMatch di dv ∧
    CallPaths incr.trace di (ProbeDerivation.result dv.probe) ∧
    CallPatch di (ProbeDerivation.result dv.probe) ∧ ProbeDerivation.Fresh di.probe ∧
    (∀ q file, FMap.get newPatch q = some (.write file) →
      ∀ q' old, (q', old) ∈ incr.records ++ witnessRecords witnesses → file.mtime ≠ old.mtime) ∧
    (∀ record ∈ patchRecords (ProbeDerivation.result di.probe).patch,
      record ∈ (incr.records ++ witnessRecords witnesses) ++ patchRecords newPatch)

theorem backward_finish (host : HostWellFormed m h)
    {witnesses : WitnessMap sig} {incr : Prefix m h .incr prog start}
    {vanilla : Prefix m h .vanilla prog start} (related : BisimRelated witnesses incr vanilla)
    (dv : StepDerivation m h .vanilla prog) (di : StepDerivation m h .incr prog)
    (before : di.before = incr.final) (matched : PaperStepsMatch di dv)
    (candidate : BackwardCall dv di.selection di.selected (incr.records ++ witnessRecords witnesses))
    (choice : ProbeDerivation.result di.probe = candidate.result ∨ ProbeDerivation.callFS di.probe = none)
    (paths : CallPaths incr.trace di candidate.result) (patch : CallPatch di candidate.result) :
    BackwardRawPair witnesses incr dv := by
  obtain ⟨newPatch, facts⟩ := backward_pack host related dv di before matched candidate choice paths patch
  exact ⟨di, newPatch, before, matched, facts⟩

/-- Every actual vanilla edge chooses a concrete Incr rule. `lem:paper-sandbox`,
`lem:paper-cache-reuse`, and `lem:paper-bisim-prefix` prove its hit guards and
path accounting; exact candidate identity proves provenance. -/
theorem backward_raw_pair (shape : DenotationShape m) (commands : WellFormedCommands m)
    (key : HashInjective m) (host : HostWellFormed m h)
    {witnesses : WitnessMap sig} {incr : Prefix m h .incr prog start}
    {vanilla full : Prefix m h .vanilla prog start} (related : BisimRelated witnesses incr vanilla)
    (properties : BisimPrefixProperties witnesses incr) (admitted : Admissible witnesses full)
    (dv : StepDerivation m h .vanilla prog) (hbefore : dv.before = vanilla.final)
    (trace : full.trace = vanilla.trace ++ [dv]) : BackwardRawPair witnesses incr dv := by
  classical
  have isolated : Isolated (vanilla.trace ++ [dv]) := trace ▸ admitted.isolated
  obtain ⟨si, wi, chosen, matching, control⟩ :=
    backward_selection host related dv.selection dv.selected (hbefore ▸ dv.host)
  obtain ⟨candidate⟩ := backward_call commands host related properties dv hbefore isolated
    chosen matching control (incr.records ++ witnessRecords witnesses)
  have cache : WellFormedCache m wi.cache := by
    rw [(host.selectionDiscipline _ _ _ incr related.incrAdmissible.operational _ _ chosen).2.2.1]
    exact related.cache
  have witnesses := selected_cache_witnesses host incr related.incrAdmissible properties chosen
  rcases dv with ⟨before, ⟨head, initialization, delivery⟩, selected, after, out, sourceHost, source⟩
  cases source with
  | openStep p i taken remaining original buffers out hb originalCall originalStatus originalFlag route =>
    obtain ⟨sb, sandbox, fsEq⟩ : ∃ sb, FMap.get wi.sandbox i = some sb ∧ candidate.fs = sb.view := by
      simpa only [CallLocation, ← matching.1] using candidate.location
    have flags := related.incrAdmissible.operational.selectedOpenSandboxes host chosen i sb sandbox
    have call : m.denotes p ⟨taken, .open⟩ sb.view wi.env candidate.result := by
      simpa only [ProbeDerivation.input, VanillaDerivation.input, Head.probe, fsEq] using candidate.call
    let ri := IncrDerivation.pipelineOpen wi p i sb taken remaining candidate.result buffers out
      (by simpa only [← control.2.2.2.1] using hb) sandbox flags.1 flags.2 call
      (candidate.status.trans originalStatus)
      (by simpa only [candidate.output, ProbeDerivation.result, VanillaDerivation.result] using originalFlag)
      (by simpa only [updateBuffer, ← control.2.2.2.1, candidate.output,
        ProbeDerivation.result, VanillaDerivation.result] using route)
    let di : StepDerivation m h .incr prog := ⟨incr.final, si, wi, _, out, chosen, castIncr matching.1 ri⟩
    have matched : PaperStepsMatch di _ := ⟨rfl, control_symm control,
      ⟨control.1.symm, control.2.1.symm, control.2.2.1.symm, rfl, control.2.2.2.2.symm⟩,
      matching.1.symm, matching.2.1.symm⟩
    have identical : ProbeDerivation.result di.probe = candidate.result :=
      incr_result_cast matching.1 ri
    have executes : ProbeDerivation.callFS di.probe = some sb.view :=
      incr_callFS_cast matching.1 ri
    apply backward_finish host related _ di rfl matched candidate (Or.inl identical)
    · exact call_paths_domains _ _ _ (by rw [identical]) (by rw [identical]) (by rw [identical])
    · simp only [CallPatch, executes, identical]
      exact ⟨rfl, fun _ _ => rfl⟩
  | closeStep p i s original es buffers out hb originalCall originalStatus originalFlag route =>
    obtain ⟨sb, sandbox, fsEq⟩ : ∃ sb, FMap.get wi.sandbox i = some sb ∧ candidate.fs = sb.view := by
      simpa only [CallLocation, ← matching.1] using candidate.location
    have flags := related.incrAdmissible.operational.selectedOpenSandboxes host chosen i sb sandbox
    have call : m.denotes p ⟨s, .eof⟩ sb.view wi.env candidate.result := by
      simpa only [ProbeDerivation.input, VanillaDerivation.input, Head.probe, fsEq] using candidate.call
    have status := candidate.status.trans originalStatus
    have flag : candidate.result.output.flag = .eof := by
      simpa only [candidate.output, ProbeDerivation.result, VanillaDerivation.result] using originalFlag
    have routing : put (selected.buffer ∖ i) i candidate.result.output = some (buffers, out) := by
      simpa only [candidate.output, ProbeDerivation.result, VanillaDerivation.result] using route
    by_cases cacheable : Cacheable m p
    · have whole := backward_folded shape commands key host related properties _ hbefore isolated
        chosen matching rfl sandbox rfl cacheable call candidate.reads candidate.writes flags.1 flags.2
      obtain ⟨after, ri, afterControl, input, produced, choice⟩ :=
        choose_cache_close shape commands key (control_symm control) cache witnesses p i sb s
          candidate.result es buffers out cacheable sandbox flags.1 flags.2 hb call status flag routing whole
      let di : StepDerivation m h .incr prog := ⟨incr.final, si, wi, after, out, chosen, castIncr matching.1 ri⟩
      have afterControl' : ControlAgree after (closeWorld selected i es original.patch buffers) := by
        simpa only [ControlAgree, closeWorld] using afterControl
      have matched : PaperStepsMatch di _ :=
        ⟨rfl, control_symm control, afterControl', matching.1.symm, matching.2.1.symm⟩
      have choice' : (ProbeDerivation.result di.probe = candidate.result ∧
          ProbeDerivation.callFS di.probe = some sb.view) ∨
          (ProbeDerivation.callFS di.probe = none ∧ ResultEquivalent
            (combineResults (sandboxResult sb) candidate.result flags.2) (ProbeDerivation.result di.probe)) := by
        simpa only [di, ProbeDerivation.result, ProbeDerivation.callFS, incr_result_cast, incr_callFS_cast] using choice
      obtain ⟨entry, init, current, slice, accounting⟩ := (properties.2.2 _ _ chosen) i sb sandbox
      have position : componentAt (incr.trace ++ [di]) incr.trace.length di = some (.pipeline entry i) := by
        rw [componentAt_snoc_last]
        simp only [di, ← matching.1, selectedComponent, current, Option.map_some]
      have facts := pipeline_choice (d := di) (by exact matching.1.symm) sandbox flags.2 position accounting choice'
      apply backward_finish host related _ di rfl matched candidate
        (choice'.elim (fun actual => Or.inl actual.1) (fun replay => Or.inr replay.1)) facts.1 facts.2
    · let ri := IncrDerivation.uncacheClose wi p i sb s candidate.result es buffers out cacheable
        (by simpa only [← control.2.2.2.1] using hb) sandbox call status flag
        (by simpa only [← control.2.2.2.1] using routing)
      let di : StepDerivation m h .incr prog := ⟨incr.final, si, wi, _, out, chosen, castIncr matching.1 ri⟩
      have matched : PaperStepsMatch di _ := ⟨rfl, control_symm control,
        ⟨control.1.symm, rfl, control.2.2.1.symm, rfl, control.2.2.2.2.symm⟩,
        matching.1.symm, matching.2.1.symm⟩
      have identical : ProbeDerivation.result di.probe = candidate.result :=
        incr_result_cast matching.1 ri
      have executes : ProbeDerivation.callFS di.probe = some sb.view :=
        incr_callFS_cast matching.1 ri
      apply backward_finish host related _ di rfl matched candidate (Or.inl identical)
      · exact call_paths_domains _ _ _ (by rw [identical]) (by rw [identical]) (by rw [identical])
      · simp only [CallPatch, executes, identical]
        exact ⟨rfl, fun _ _ => rfl⟩
  | standalone p s original es stdin originalCall originalStatus =>
    have fsEq : candidate.fs = wi.fs := by
      simpa only [CallLocation, ← matching.1] using candidate.location
    have call : m.denotes p ⟨s, .eof⟩ wi.fs wi.env candidate.result := by
      simpa only [ProbeDerivation.input, VanillaDerivation.input, Head.probe, fsEq] using candidate.call
    obtain ⟨after, out, ri, afterControl, output, input, produced, choice⟩ :=
      choose_standalone shape commands key (control_symm control) cache witnesses p s candidate.result es
        stdin call (candidate.status.trans originalStatus)
    let di : StepDerivation m h .incr prog := ⟨incr.final, si, wi, after, out, chosen, castIncr matching.1 ri⟩
    have matched : PaperStepsMatch di _ :=
      ⟨output.trans (congrArg some candidate.output), control_symm control,
        by simpa only [ControlAgree, standaloneWorld] using afterControl,
        matching.1.symm, matching.2.1.symm⟩
    have choice' : ProbeDerivation.result di.probe = candidate.result ∨
        (ProbeDerivation.callFS di.probe = none ∧ ResultEquivalent candidate.result (ProbeDerivation.result di.probe)) := by
      simpa only [di, ProbeDerivation.result, ProbeDerivation.callFS, incr_result_cast, incr_callFS_cast] using choice
    have facts := standalone_choice (trace := incr.trace) (d := di) matching.1.symm choice'
    exact backward_finish host related _ di rfl matched candidate
      (choice'.elim Or.inl (fun replay => Or.inr replay.1)) facts.1 facts.2

theorem vanilla_after_fs {w after : World sig} {head : Head sig} {out : Option Chunk}
    (d : VanillaDerivation m w head after out) : after.fs = applyPatch w.fs (VanillaDerivation.result d).patch := by
  cases d <;> rfl

/-- Actual successor isolation separates each executed or reconstructed call from
all other staged patches. Closed components stay in the isolation comparison. -/
theorem pipeline_separated {trace : Trace m h .incr prog} (d : StepDerivation m h .incr prog)
    (slices : LiveSliceProperties trace d.selected (selectedPipeline trace d.selection))
    (isolated : Isolated (trace ++ [d])) {p : sig.Probe} {i : Nat} {sb : Sandbox sig}
    (head : d.selection.head = .pipeline p i) (sandbox : FMap.get d.selected.sandbox i = some sb)
    (call : Patch sig) (support : FMap.dom call ⊆ FMap.dom (ProbeDerivation.result d.probe).patch) :
    ∀ j other, j ≠ i → FMap.get d.selected.sandbox j = some other →
      Disjoint (FMap.dom call) (FMap.dom other.patch) := by
  obtain ⟨entry, init, current, slice, accounting⟩ := slices i sb sandbox
  have position : componentAt (trace ++ [d]) trace.length d = some (.pipeline entry i) := by
    rw [componentAt_snoc_last, head]
    simp only [selectedComponent, current, Option.map_some]
  apply OverlayUpdates.source_separation isolated entry i call d.selected
  · intro q member
    exact ⟨d, snoc_member trace d position, support member⟩
  · intro j other different get q member
    obtain ⟨entry', init', current', otherSlice, _⟩ := slices j other get
    have same := Option.some.inj (current.symm.trans current')
    cases same
    rw [← otherSlice.1] at member
    obtain ⟨old, oldMember, path⟩ := member
    exact ⟨old, C9.componentSteps_append_subset trace [d] _ old oldMember, path⟩

/-- All raw matched cases preserve the full pending-overlay relation. -/
theorem raw_post_overlay (host : HostWellFormed m h)
    {witnesses : WitnessMap sig} {incr : Prefix m h .incr prog start}
    {vanilla : Prefix m h .vanilla prog start} (related : BisimRelated witnesses incr vanilla)
    (properties : BisimPrefixProperties witnesses incr)
    (di : StepDerivation m h .incr prog) (dv : StepDerivation m h .vanilla prog)
    (beforeI : di.before = incr.final) (beforeV : dv.before = vanilla.final)
    (matched : PaperStepsMatch di dv) (patch : CallPatch di (ProbeDerivation.result dv.probe))
    (isolated : Isolated (incr.trace ++ [di])) :
    FSApprox dv.after.fs (applyPatch di.after.fs (pendingPatch di.after)) := by
  classical
  have chosenI : h.select prog incr.final di.selection di.selected := beforeI ▸ di.host
  have chosenV : h.select prog vanilla.final dv.selection dv.selected := beforeV ▸ dv.host
  have overlay := selected_overlay host related chosenI chosenV
  have discipline := host.selectionDiscipline _ _ _ incr related.incrAdmissible.operational _ _ chosenI
  have disjoint := OverlayUpdates.selection_disjoint discipline related.disjointPatches
  have slices := properties.2.2 _ _ chosenI
  rw [vanilla_after_fs dv.probe]
  rcases di with ⟨before, ⟨head, initialization, delivery⟩, selected, after, out, chosen, derivation⟩
  cases derivation with
  | pipelineOpen p i sb taken remaining r buffers out hb hs hi ho call status flag route =>
    have patch' : PatchApprox (ProbeDerivation.result dv.probe).patch r.patch := patch
    have separated := pipeline_separated _ slices isolated rfl hs r.patch (fun _ member => member)
    have result := OverlayUpdates.post_open selected dv.selected.fs i sb hs disjoint
      ⟨taken, .open⟩ r hi ho (ProbeDerivation.result dv.probe).patch overlay patch' separated
    simpa only [updateWorld_none_empty, updateSandbox, pendingPatch, ProbeDerivation.result] using result
  | uncacheClose p i sb s r es buffers out hc hb hs call status flag route =>
    have patch' : PatchApprox (ProbeDerivation.result dv.probe).patch r.patch := patch
    have separated := pipeline_separated _ slices isolated rfl hs r.patch (fun _ member => member)
    have result := OverlayUpdates.post_close selected dv.selected.fs i sb hs disjoint
      r.patch (ProbeDerivation.result dv.probe).patch (sb.patch ⊎ r.patch) overlay patch'
      ⟨rfl, fun _ _ => rfl⟩ separated
    simpa only [closeWorld, pendingPatch, ProbeDerivation.result] using result
  | cacheCloseMiss p i sb s r es buffers out hc hb hs hi ho miss call status flag route =>
    have patch' : PatchApprox (ProbeDerivation.result dv.probe).patch r.patch := patch
    have separated := pipeline_separated _ slices isolated rfl hs r.patch (fun _ member => member)
    have result := OverlayUpdates.post_close selected dv.selected.fs i sb hs disjoint
      r.patch (ProbeDerivation.result dv.probe).patch (sb.patch ⊎ r.patch) overlay patch'
      ⟨rfl, fun _ _ => rfl⟩ separated
    simpa only [updateWorld, pendingPatch, ProbeDerivation.result] using result
  | cacheCloseHit p i sb s tail memo buffers out hc hb hs hi ho entry valid guard route =>
    have patch' : PatchApprox (sb.patch ⊎ (ProbeDerivation.result dv.probe).patch) memo.patch := patch sb hs
    have support : FMap.dom (ProbeDerivation.result dv.probe).patch ⊆ FMap.dom memo.patch := by
      rw [← patch'.1, FMap.dom_merge]
      exact Set.subset_union_right
    have separated := pipeline_separated _ slices isolated rfl hs (ProbeDerivation.result dv.probe).patch support
    have result := OverlayUpdates.post_close selected dv.selected.fs i sb hs disjoint
      (ProbeDerivation.result dv.probe).patch (ProbeDerivation.result dv.probe).patch memo.patch overlay
      ⟨rfl, fun _ _ => rfl⟩ (patch_symm patch') separated
    simpa only [updateWorld, pendingPatch, ProbeDerivation.result] using result
  | uncacheStandalone p s r es hc stdin call status =>
    have empty := (OverlayUpdates.standalone_pending discipline rfl).2
    have afterEmpty : pendingPatch (standaloneWorld selected es r.patch) = ∅ := empty
    rw [empty, (patch_algebra (sig := sig)).2.1] at overlay
    rw [afterEmpty, (patch_algebra (sig := sig)).2.1]
    exact (patch_algebra (sig := sig)).2.2.2.1 _ _ _ _ overlay patch
  | cacheStandaloneMiss p s r es hc stdin miss call status flag =>
    have empty := (OverlayUpdates.standalone_pending discipline rfl).2
    have afterEmpty : pendingPatch {standaloneWorld selected es r.patch with
        cache := FMap.set selected.cache (cacheKey m p selected.env ⟨s, .eof⟩)
          ⟨es, r.patch, r.reads, r.writes, r.output, flag⟩} = ∅ := empty
    rw [empty, (patch_algebra (sig := sig)).2.1] at overlay
    rw [afterEmpty, (patch_algebra (sig := sig)).2.1]
    exact (patch_algebra (sig := sig)).2.2.2.1 _ _ _ _ overlay patch
  | cacheStandaloneHit p s memo hc stdin entry valid flag =>
    have empty := (OverlayUpdates.standalone_pending discipline rfl).2
    have afterEmpty : pendingPatch (standaloneWorld selected memo.ec memo.patch) = ∅ := empty
    rw [empty, (patch_algebra (sig := sig)).2.1] at overlay
    rw [afterEmpty, (patch_algebra (sig := sig)).2.1]
    exact (patch_algebra (sig := sig)).2.2.2.1 _ _ _ _ overlay patch

theorem vanilla_after_cache {w after : World sig} {head : Head sig} {out : Option Chunk}
    (d : VanillaDerivation m w head after out) : after.cache = w.cache := by
  cases d <;> rfl

/-- Append one actual whole derivation to a raw prefix. Admission remains separate. -/
def snocPrefix {executor : Executor} (pre : Prefix m h executor prog start)
    (d : StepDerivation m h executor prog) (before : d.before = pre.final) :
    Prefix m h executor prog start :=
  ⟨pre.trace ++ [d], d.after, pre.initial,
    C9.connected_append (before.symm ▸ pre.connected) (.cons d [] d.after (.nil d.after))⟩

/-- Once both concrete successors are admitted, `lem:paper-buffers` and
`lem:paper-sandbox`, together with the raw matching certificates, establish every
field of the original `def:paper-bisim-relation` relation. -/
theorem related_snoc (shape : DenotationShape m) (commands : WellFormedCommands m)
    (key : HashInjective m) (host : HostWellFormed m h) (cache : WellFormedCache m start.cache)
    {witnesses : WitnessMap sig} {incr nextI : Prefix m h .incr prog start}
    {vanilla nextV : Prefix m h .vanilla prog start} (related : BisimRelated witnesses incr vanilla)
    (properties : BisimPrefixProperties witnesses incr)
    (di : StepDerivation m h .incr prog) (dv : StepDerivation m h .vanilla prog)
    (traceI : nextI.trace = incr.trace ++ [di]) (traceV : nextV.trace = vanilla.trace ++ [dv])
    (beforeI : di.before = incr.final) (beforeV : dv.before = vanilla.final)
    (afterI : di.after = nextI.final) (afterV : dv.after = nextV.final)
    (admittedI : Admissible witnesses nextI) (admittedV : Admissible witnesses nextV)
    (matched : PaperStepsMatch di dv) (accounting : CallPaths incr.trace di (ProbeDerivation.result dv.probe))
    (patch : CallPatch di (ProbeDerivation.result dv.probe)) : BisimRelated witnesses nextI nextV := by
  have stateI := (buffer_sandbox_preservation shape commands key host nextI admittedI.operational).1
  have stateV := (buffer_sandbox_preservation shape commands key host nextV admittedV.operational).1
  have preservation := cacheable_prefixes shape commands key host cache nextI admittedI.operational
  have controls : ControlAgree nextI.final nextV.final := by
    simpa only [afterI, afterV] using matched.2.2.1
  refine {
    incrAdmissible := admittedI
    vanillaAdmissible := admittedV
    equalLength := ?_
    steps := ?_
    cache := preservation.1
    vanillaCache := ?_
    sandboxDomains := stateI.1.symm.trans ((congrArg FMap.dom controls.2.2.2.1).trans stateV.1)
    vanillaEmpty := admittedV.operational.vanilla_initial_fields host
    incrSandboxes := stateI
    incrPrefixes := preservation.2.1
    disjointPatches := OverlayUpdates.disjoint_of_state stateI admittedI.isolated
    overlay := ?_
    paths := ?_
  }
  · rw [traceI, traceV]
    simp only [List.length_append, List.length_singleton, related.equalLength]
  · rw [traceI, traceV]
    have append {left : Trace m h .incr prog} {right : Trace m h .vanilla prog}
        (paired : List.Forall₂ PaperStepsMatch left right) :
        List.Forall₂ PaperStepsMatch (left ++ [di]) (right ++ [dv]) := by
      induction paired with
      | nil => exact .cons matched .nil
      | cons step rest ih => exact .cons step ih
    exact append related.steps
  · rw [← afterV, vanilla_after_cache dv.probe]
    have selected := host.selectionDiscipline _ _ _ vanilla related.vanillaAdmissible.operational
      dv.selection dv.selected (beforeV ▸ dv.host)
    exact selected.2.2.1.trans related.vanillaCache
  · have isolated : Isolated (incr.trace ++ [di]) := traceI ▸ admittedI.isolated
    have overlay := raw_post_overlay host related properties di dv beforeI beforeV matched patch isolated
    simpa only [afterI, afterV] using overlay
  · rw [traceI, traceV]
    exact paths_snoc related.steps related.paths matched accounting

/-- Forward `thm:paper-bisimulation` step simulation with the exact original
assumptions and relation. -/
theorem forward_steps (_initial : Initial h prog start) (shape : DenotationShape m)
    (commands : WellFormedCommands m) (key : HashInjective m) (host : HostWellFormed m h)
    (cache : WellFormedCache m start.cache) (witnesses : WitnessMap sig)
    (initialWitnesses : WitnessesFor m start.cache witnesses)
    (initialRecords : TimestampConsistent (worldPaperRecords start ∪ witnessPaperRecords witnesses))
    (incr full : Prefix m h .incr prog start) (vanilla : Prefix m h .vanilla prog start)
    (label : Head sig) (related : BisimRelated witnesses incr vanilla)
    (edge : PrefixStep witnesses label incr full) :
    ∃ next : Prefix m h .vanilla prog start,
      PrefixStep witnesses label vanilla next ∧ BisimRelated witnesses full next := by
  obtain ⟨_, admitted, di, traceI, beforeI, afterI, labeled⟩ := edge
  have properties := PrefixProperties.paper_bisim_prefix shape commands key host cache witnesses initialWitnesses initialRecords
    incr related.incrAdmissible
  obtain ⟨dv, beforeV, matched, paths, patch, fresh, avoid⟩ :=
    forward_raw_pair shape commands key host cache related properties admitted di beforeI traceI
  let next := snocPrefix vanilla dv beforeV
  have allPaths := paths_snoc related.steps related.paths matched paths
  have isolated : Isolated next.trace :=
    (isolation_transport allPaths).mp (traceI ▸ admitted.isolated)
  have admittedV : Admissible witnesses next := RecordInventory.admissible_snoc host
    related.vanillaAdmissible dv rfl beforeV fresh isolated (ProbeDerivation.result dv.probe).patch avoid
    (fun record member => List.mem_append_right _ member)
  refine ⟨next, ⟨related.vanillaAdmissible, admittedV, dv, rfl, beforeV, rfl,
    matched.2.2.2.1.symm.trans labeled⟩, ?_⟩
  exact related_snoc shape commands key host cache related properties di dv traceI rfl beforeI beforeV
    afterI rfl admitted admittedV matched paths patch

/-- Backward `thm:paper-bisimulation` step simulation with actual cache choices and
complete admission. -/
theorem backward_steps (_initial : Initial h prog start) (shape : DenotationShape m)
    (commands : WellFormedCommands m) (key : HashInjective m) (host : HostWellFormed m h)
    (cache : WellFormedCache m start.cache) (witnesses : WitnessMap sig)
    (initialWitnesses : WitnessesFor m start.cache witnesses)
    (initialRecords : TimestampConsistent (worldPaperRecords start ∪ witnessPaperRecords witnesses))
    (vanilla full : Prefix m h .vanilla prog start) (incr : Prefix m h .incr prog start)
    (label : Head sig) (related : BisimRelated witnesses incr vanilla)
    (edge : PrefixStep witnesses label vanilla full) :
    ∃ next : Prefix m h .incr prog start,
      PrefixStep witnesses label incr next ∧ BisimRelated witnesses next full := by
  obtain ⟨_, admitted, dv, traceV, beforeV, afterV, labeled⟩ := edge
  have properties := PrefixProperties.paper_bisim_prefix shape commands key host cache witnesses initialWitnesses initialRecords
    incr related.incrAdmissible
  obtain ⟨di, newPatch, beforeI, matched, paths, patch, fresh, avoid, sources⟩ :=
    backward_raw_pair shape commands key host related properties admitted dv beforeV traceV
  let next := snocPrefix incr di beforeI
  have allPaths := paths_snoc related.steps related.paths matched paths
  have isolated : Isolated next.trace :=
    (isolation_transport allPaths).mpr (traceV ▸ admitted.isolated)
  have admittedI : Admissible witnesses next := RecordInventory.admissible_snoc host
    related.incrAdmissible di rfl beforeI fresh isolated newPatch avoid sources
  refine ⟨next, ⟨related.incrAdmissible, admittedI, di, rfl, beforeI, rfl,
    matched.2.2.2.1.trans labeled⟩, ?_⟩
  exact related_snoc shape commands key host cache related properties di dv rfl traceV beforeI beforeV
    rfl afterV admittedI admitted matched paths patch

end
end Incr.Incr.C8Steps


