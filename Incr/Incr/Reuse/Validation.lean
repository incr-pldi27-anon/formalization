import Incr.Incr.Reuse.Statements

/-! # Cache validation and reuse (`lem:paper-cache-reuse`) -/

open Incr
namespace Incr.Incr

variable {sig : Signature} {m : CommandModel sig} {h : Host sig}
  {prog : sig.Prog} {start : World sig}

/-- `lem:paper-cache-reuse` (validation and cache reuse): the relevant entry's
local witness filesystem. No chosen data for unrelated cache entries occurs in
this interface. -/
theorem validation_and_cache_reuse (_shape : DenotationShape m)
    (_commands : WellFormedCommands m) (_key : HashInjective m)
    (cache : Cache sig) (_cache : WellFormedCache m cache)
    (p : sig.Probe) (env : Env sig) (input : Chunk) (memo : Memo sig)
    (witnessFS fs : FS sig)
    (_eof : input.flag = .eof)
    (_entry : FMap.get cache (cacheKey m p env input) = some memo)
    (_witness : EntryWitness m (cacheKey m p env input) memo witnessFS)
    (_valid : Valid m memo.reads memo.writes fs)
    (_timestamps : TimestampConsistent ({recordOfFS witnessFS} ∪ {recordOfFS fs})) :
    CacheReuseResult m p env input memo witnessFS fs := by
  classical
  have normalizedTimestamps := (two_filesystems_consistent_iff witnessFS fs).mp _timestamps
  obtain ⟨historicalProbe, historicalEnv, historicalInput, cacheable, _, keyEq,
    historicalDenotes⟩ := _witness
  have probeEq : p = historicalProbe := congrArg Key.probe keyEq
  have envEq : env = historicalEnv := congrArg Key.env keyEq
  have inputEq : input = historicalInput :=
    Sum.inl.inj (_key (congrArg Key.inputHash keyEq))
  subst historicalProbe
  subst historicalEnv
  subst historicalInput
  have witnessValid : Valid m memo.reads memo.writes witnessFS :=
    _commands.dependencies.valid p input witnessFS env memo.result historicalDenotes
  have agreement : DepAgree memo.reads memo.writes witnessFS fs := by
    refine ⟨fun q hq => ⟨witnessValid.1 hq, _valid.1 hq⟩, ?_, ?_⟩
    · intro q hq
      obtain ⟨time, read⟩ := Finmap.mem_iff.mp (Finmap.mem_keys.mp hq)
      obtain ⟨old, oldGet⟩ := Finmap.mem_iff.mp
        (Finmap.mem_keys.mp (witnessValid.1 (Or.inl hq)))
      obtain ⟨live, liveGet⟩ := Finmap.mem_iff.mp
        (Finmap.mem_keys.mp (_valid.1 (Or.inl hq)))
      change FMap.get witnessFS q = some old at oldGet
      change FMap.get fs q = some live at liveGet
      have oldTime := witnessValid.2.1 q time old read oldGet
      have liveTime := _valid.2.1 q time live read liveGet
      have sameTime : old.mtime = live.mtime := oldTime.trans liveTime.symm
      have sameContent : old.content = live.content :=
        normalizedTimestamps q old live
          (List.mem_append_left _ (mem_fsRecords_of_get oldGet))
          (List.mem_append_right _ (mem_fsRecords_of_get liveGet)) sameTime
      rw [oldGet, liveGet, File.ext sameContent sameTime]
    · intro q hq
      obtain ⟨hash, write⟩ := Finmap.mem_iff.mp (Finmap.mem_keys.mp hq)
      obtain ⟨old, oldGet⟩ := Finmap.mem_iff.mp
        (Finmap.mem_keys.mp (witnessValid.1 (Or.inr hq)))
      obtain ⟨live, liveGet⟩ := Finmap.mem_iff.mp
        (Finmap.mem_keys.mp (_valid.1 (Or.inr hq)))
      change FMap.get witnessFS q = some old at oldGet
      change FMap.get fs q = some live at liveGet
      have oldHash := witnessValid.2.2 q hash old write oldGet
      have liveHash := _valid.2.2 q hash live write liveGet
      have sameContent : old.content = live.content :=
        Sum.inr.inj (_key (oldHash.trans liveHash.symm))
      simp only [oldGet, liveGet, Option.map_some, sameContent]
  obtain ⟨⟨result, denotes⟩, equivalent⟩ :=
    cacheable input witnessFS env memo.result historicalDenotes fs agreement
  have resultEq := equivalent result denotes
  have exactPatch : PatchApprox memo.patch result.patch :=
    ⟨resultEq.2.1.symm, fun q hq => by
      have hq' : q ∈ FMap.dom result.patch := by rw [resultEq.2.1]; exact hq
      exact (resultEq.2.2 q hq').symm⟩
  have exactDenotes :=
    _commands.timestamps.retimestamp p input fs env result denotes memo.patch exactPatch
  have exactResult : { result with patch := memo.patch } = memo.result := by
    have fields := resultEq.1
    cases result
    cases memo
    simp_all [Memo.result]
  rw [exactResult] at exactDenotes
  exact ⟨agreement, exactDenotes, equivalent⟩

end Incr.Incr
