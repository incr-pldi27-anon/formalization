import Incr.IncrPP.Preservation.Proof

/-!
# Open live entries and local cache validation

These facts use actual selected boundaries and the shared mathematical
command/cache definitions, not the completed Incr 1.0 executor.
-/

namespace Incr.IncrPP

noncomputable section

variable {sig : Signature} {m : CommandModel sig} {h : Host sig}
  {prog : sig.Prog} {start : World sig}

/-- Every currently allocated live payload has open cumulative input and output. -/
def LiveOpenFlags (pre : Prefix m h .live prog start) (b : Boundary pre) : Prop :=
  ∀ entry slot sb, b.livePipeline entry slot → FMap.get b.world.sandbox slot = some sb →
    sb.input.flag = .open ∧ sb.output.flag = .open

/-- A permitted selection retains open flags or creates an initial payload. -/
theorem LiveOpenFlags.selected (pre : Prefix m h .live prog start)
    (flags : LiveOpenFlags pre .final) (selection : Selection sig) (world : World sig)
    (allowed : h.select prog pre.final selection world)
    (discipline : SelectionDiscipline pre.trace pre.final selection world) :
    LiveOpenFlags pre (.selected selection world allowed) := by
  intro entry slot sb live present
  rcases discipline with ⟨_, _, _, allocation, _⟩
  cases initializes : selection.init with
  | none =>
    simp only [initializes] at allocation
    have oldLive : (Boundary.final : Boundary pre).livePipeline entry slot := by
      simpa [Boundary.livePipeline, Boundary.currentEntry, Boundary.componentDomain,
        Boundary.selection?, initializes] using live
    have old : FMap.get pre.final.sandbox slot = some sb := by
      simpa only [Boundary.world, allocation.1] using present
    exact flags entry slot sb oldLive old
  | some init =>
    simp only [initializes] at allocation
    have initial : sb = Sandbox.initial pre.final.fs := by
      apply initialSandboxes_value init pre.final.fs
      simpa only [Boundary.world, allocation.2.2.2.2] using present
    subst sb
    exact ⟨rfl, rfl⟩

/-- Actual open rules maintain open flags; foreign rules keep the payload unchanged. -/
theorem LiveOpenFlags.after_step (shape : DenotationShape m)
    (pre post : Prefix m h .live prog start) (d : StepDerivation m h .live prog)
    (allowed : h.select prog pre.final d.selection d.selected)
    (joined : post.trace = pre.trace ++ [d]) (after : post.final = d.after)
    (flags : LiveOpenFlags pre (.selected d.selection d.selected allowed)) : LiveOpenFlags post .final := by
  intro entry slot sb live present
  have oldLive := ((Boundary.livePipeline_after_step pre post d allowed joined entry slot).mp live).1
  have actual : FMap.get d.after.sandbox slot = some sb := by
    simpa only [Boundary.world, after] using present
  rcases LiveDerivation.history_effect d.probe actual with own | foreign
  · obtain ⟨p, head, openInput, old, hin, hout, prior, rfl⟩ := own
    have call := d.probe.open_call head openInput
    have outputOpen := (shape p _ _ _ _ call.1).1 openInput |>.1
    exact ⟨by simpa using openInput, by simpa using outputOpen⟩
  · obtain ⟨prior, _⟩ := foreign
    exact flags entry slot sb oldLive prior

/-- Open flags hold at every operational live endpoint and permitted selection. -/
theorem Operational.liveOpenFlags (shape : DenotationShape m) (host : HostWellFormed m h)
    (pre : Prefix m h .live prog start) (operational : Operational pre) (b : Boundary pre) : LiveOpenFlags pre b := by
  have endpoint : LiveOpenFlags pre .final := by
    apply Operational.snoc_induction (fun pre => LiveOpenFlags pre .final) ?_ ?_ pre operational
    · intro pre _ empty entry slot sb _ present
      have connected := pre.connected
      rw [empty] at connected
      have endpoint := (Connected.nil_iff start pre.final).mp connected
      simp [Boundary.world, endpoint, pre.initial.2.1, FMap.get] at present
    · intro short post d shortOperational _ joined before after ih
      have allowed : h.select prog short.final d.selection d.selected := by simpa only [before] using d.host
      have discipline := host.selectionDiscipline .live prog start short shortOperational d.selection d.selected allowed
      exact LiveOpenFlags.after_step shape short post d allowed joined after
        (LiveOpenFlags.selected short ih d.selection d.selected allowed discipline)
  cases b with
  | final => exact endpoint
  | selected selection world allowed =>
    exact LiveOpenFlags.selected pre endpoint selection world allowed
      (host.selectionDiscipline .live prog start pre operational selection world allowed)

/-- A valid memo with a locally consistent witness denotes its exact whole-input result. -/
theorem validated_memo (commands : WellFormedCommands m) (hash : HashInjective m)
    (p : sig.Probe) (env : Env sig) (input : Chunk) (memo : Memo sig) (witness fs : FS sig)
    (certificate : EntryWitness m (cacheKey m p env input) memo witness)
    (valid : Valid m memo.reads memo.writes fs)
    (consistent : TimestampConsistent ({recordOfFS witness} ∪ {recordOfFS fs})) :
    m.denotes p input fs env memo.result ∧
      ∀ result, m.denotes p input fs env result → ResultEquivalent memo.result result := by
  have normalized := (two_filesystems_consistent_iff witness fs).mp consistent
  obtain ⟨historicalProbe, historicalEnv, historicalInput, cacheable, _, keyEq,
    historicalDenotes⟩ := certificate
  have probeEq : p = historicalProbe := congrArg Key.probe keyEq
  have envEq : env = historicalEnv := congrArg Key.env keyEq
  have inputEq : input = historicalInput := Sum.inl.inj (hash (congrArg Key.inputHash keyEq))
  subst historicalProbe
  subst historicalEnv
  subst historicalInput
  have witnessValid : Valid m memo.reads memo.writes witness :=
    commands.dependencies.valid p input witness env memo.result historicalDenotes
  have agreement : DepAgree memo.reads memo.writes witness fs := by
    refine ⟨fun q hq => ⟨witnessValid.1 hq, valid.1 hq⟩, ?_, ?_⟩
    · intro q hq
      obtain ⟨time, read⟩ := Finmap.mem_iff.mp (Finmap.mem_keys.mp hq)
      obtain ⟨old, oldGet⟩ := Finmap.mem_iff.mp (Finmap.mem_keys.mp (witnessValid.1 (Or.inl hq)))
      obtain ⟨live, liveGet⟩ := Finmap.mem_iff.mp (Finmap.mem_keys.mp (valid.1 (Or.inl hq)))
      change FMap.get witness q = some old at oldGet
      change FMap.get fs q = some live at liveGet
      have oldTime := witnessValid.2.1 q time old read oldGet
      have liveTime := valid.2.1 q time live read liveGet
      have sameTime : old.mtime = live.mtime := oldTime.trans liveTime.symm
      have sameContent : old.content = live.content :=
        normalized q old live (List.mem_append_left _ (mem_fsRecords_of_get oldGet))
          (List.mem_append_right _ (mem_fsRecords_of_get liveGet)) sameTime
      rw [oldGet, liveGet, File.ext sameContent sameTime]
    · intro q hq
      obtain ⟨content, write⟩ := Finmap.mem_iff.mp (Finmap.mem_keys.mp hq)
      obtain ⟨old, oldGet⟩ := Finmap.mem_iff.mp (Finmap.mem_keys.mp (witnessValid.1 (Or.inr hq)))
      obtain ⟨live, liveGet⟩ := Finmap.mem_iff.mp (Finmap.mem_keys.mp (valid.1 (Or.inr hq)))
      change FMap.get witness q = some old at oldGet
      change FMap.get fs q = some live at liveGet
      have oldHash := witnessValid.2.2 q content old write oldGet
      have liveHash := valid.2.2 q content live write liveGet
      have sameContent : old.content = live.content := Sum.inr.inj (hash (oldHash.trans liveHash.symm))
      simp only [oldGet, liveGet, Option.map_some, sameContent]
  obtain ⟨⟨result, denotes⟩, equivalent⟩ :=
    cacheable input witness env memo.result historicalDenotes fs agreement
  have resultEq := equivalent result denotes
  have exactPatch : PatchApprox memo.patch result.patch :=
    ⟨resultEq.2.1.symm, fun q hq => by
      have hq' : q ∈ FMap.dom result.patch := by rw [resultEq.2.1]; exact hq
      exact (resultEq.2.2 q hq').symm⟩
  have exactDenotes := commands.timestamps.retimestamp p input fs env result denotes memo.patch exactPatch
  have exactResult : { result with patch := memo.patch } = memo.result := by
    have fields := resultEq.1
    cases result
    cases memo
    simp_all [Memo.result]
  rw [exactResult] at exactDenotes
  exact ⟨exactDenotes, equivalent⟩

/-- A permitted selection retains the first environment without requiring a future probe. -/
theorem FirstEnvironment.boundary_env (host : HostWellFormed m h)
    (pre : Prefix m h .live prog start) (operational : Operational pre)
    (selection : Selection sig) (world : World sig) (allowed : h.select prog pre.final selection world)
    (entry slot : Nat) (p : sig.Probe) (head : selection.head = .pipeline p slot)
    (live : (Boundary.selected selection world allowed).livePipeline entry slot)
    (env : Env sig) (first : FirstEnvironment pre.trace (.pipeline entry slot) env) : world.env = env := by
  obtain ⟨firstStep, firstAt, envEq⟩ := first
  have member : firstStep ∈ componentSteps pre.trace (.pipeline entry slot) := List.mem_of_head? firstAt
  have entryLt : entry < pre.trace.length := by
    by_contra notLt
    have fresh := componentSteps_fresh pre.trace entry slot (Nat.le_of_not_gt notLt)
    simp [fresh] at member
  have noInit : selection.init = none := by
    cases initializes : selection.init with
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
    ⟨Boundary.pipelineDomain_old pre selection world allowed entryLt live.2.1, live.2.2⟩
  have selected := host.componentSelectionEnvironments .live prog start pre operational
    selection world allowed p slot entry firstStep noInit head historical currentSlot member
  exact selected.trans envEq

/-- A well-formed finite cache admits fixed witness choices for all its entries. -/
theorem WellFormedCache.exists_witnesses (cache : Cache sig) (wellFormed : WellFormedCache m cache) :
    ∃ witnesses : WitnessMap sig, WitnessesFor m cache witnesses := by
  classical
  have existsChoice : ∀ key memo, FMap.get cache key = some memo →
      ∃ witness : CacheWitness sig, ∃ p env, Cacheable m p ∧ witness.input.flag = .eof ∧
        key = cacheKey m p env witness.input ∧ m.denotes p witness.input witness.fs env memo.result := by
    intro key memo found
    obtain ⟨p, env, input, fs, cacheable, eof, keyEq, call⟩ := wellFormed key memo found
    exact ⟨⟨input, fs⟩, p, env, cacheable, eof, keyEq, call⟩
  let chooseWitness : Key sig → Memo sig → CacheWitness sig := fun key memo =>
    if found : FMap.get cache key = some memo then Classical.choose (existsChoice key memo found)
    else ⟨Chunk.emptyEOF, ∅⟩
  let witnesses : WitnessMap sig := FMap.filterMap (fun key memo => some (chooseWitness key memo)) cache
  refine ⟨witnesses, ?_, ?_⟩
  · ext key
    constructor
    · intro member
      obtain ⟨witness, found⟩ := Finmap.mem_iff.mp (Finmap.mem_keys.mp member)
      change FMap.get witnesses key = some witness at found
      rw [show FMap.get witnesses key = (FMap.get cache key).bind (fun memo => some (chooseWitness key memo)) from
        FMap.get_filterMap _ _ _] at found
      cases cacheAt : FMap.get cache key with
      | none => simp [cacheAt] at found
      | some memo => exact Finmap.mem_keys.mpr (Finmap.mem_iff.mpr ⟨memo, cacheAt⟩)
    · intro member
      obtain ⟨memo, found⟩ := Finmap.mem_iff.mp (Finmap.mem_keys.mp member)
      change FMap.get cache key = some memo at found
      apply Finmap.mem_keys.mpr
      apply Finmap.mem_iff.mpr
      refine ⟨chooseWitness key memo, ?_⟩
      change FMap.get witnesses key = some (chooseWitness key memo)
      rw [show FMap.get witnesses key = (FMap.get cache key).bind (fun memo => some (chooseWitness key memo)) from
        FMap.get_filterMap _ _ _, found]
      rfl
  · intro key memo found
    refine ⟨chooseWitness key memo, ?_, ?_⟩
    · rw [show FMap.get witnesses key = (FMap.get cache key).bind (fun memo => some (chooseWitness key memo)) from
        FMap.get_filterMap _ _ _, found]
      rfl
    · simpa [chooseWitness, found] using Classical.choose_spec (existsChoice key memo found)

end
end IncrPP
end Incr
