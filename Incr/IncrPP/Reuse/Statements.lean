import Incr.IncrPP.Reuse.HitPrelude

/-!
# E.7: live cache-hit completion

The statement assumes memo lookup and validation, not an actual hit rule or
its output-prefix guard. Output-concatenation definedness is a conclusion,
not a caller premise. Fresh choice and both cumulative path sets remain explicit.
-/
namespace Incr.IncrPP

open Incr
noncomputable section
variable {sig : Signature} {m : CommandModel sig} {h : Host sig}
  {prog : sig.Prog} {start : World sig}

/-- The equations in E.7, plus its explicit after-close path accounting. -/
def ClosingMatch (pre : Prefix m h .live prog start) (b : Boundary pre)
    (entry i : Nat) (p : sig.Probe) (sb : Sandbox sig) (s : Bytes) (memo : Memo sig)
    (hout : sb.output.flag = .open) (tail : Bytes) (patch : Patch sig)
    (reads : Reads sig) (writes : Writes sig) : Prop :=
  m.denotes p ⟨s, .eof⟩ b.world.fs b.world.env
    ⟨some memo.ec, patch, reads, writes, ⟨tail, .eof⟩⟩ ∧
  memo.output = sb.output ++'hout ⟨tail, .eof⟩ ∧ PatchApprox patch memo.patch ∧
  sb.reads ⊎ reads = memo.reads ∧ sb.writes ⊎ writes = memo.writes ∧
  (componentWrites pre.trace (.pipeline entry i) ∪ FMap.dom memo.patch =
    componentWrites pre.trace (.pipeline entry i) ∪ FMap.dom patch) ∧
  (componentAccesses pre.trace (.pipeline entry i) ∪
      (FMap.dom memo.patch ∪ FMap.dom memo.reads ∪ FMap.dom memo.writes) =
    componentAccesses pre.trace (.pipeline entry i) ∪
      (FMap.dom patch ∪ FMap.dom reads ∪ FMap.dom writes))

/-- Both the ordinary existential and the finite-set-fresh existential are retained. -/
structure HitCompletion (pre : Prefix m h .live prog start) (b : Boundary pre)
    (entry i : Nat) (p : sig.Probe) (sb : Sandbox sig) (s : Bytes) (memo : Memo sig)
    (hout : sb.output.flag = .open) : Prop where
  closing : ∃ tail patch reads writes, ClosingMatch pre b entry i p sb s memo hout tail patch reads writes
  fresh : ∀ avoid : Set sig.MTime, avoid.Finite → ∃ tail patch reads writes,
    ClosingMatch pre b entry i p sb s memo hout tail patch reads writes ∧
      ∀ q file, FMap.get patch q = some (.write file) → file.mtime ∉ avoid

/-- A fresh closing call and whole-input comparison imply every printed E.7 equation. -/
theorem closingMatch_of_fold (shape : DenotationShape m) (commands : WellFormedCommands m)
    (pre : Prefix m h .live prog start) (b : Boundary pre) (entry i : Nat)
    (p : sig.Probe) (sb : Sandbox sig) (s : Bytes) (memo : Memo sig)
    (hin : sb.input.flag = .open) (hout : sb.output.flag = .open) (empty : sb.patch = ∅)
    (paths : componentAccesses pre.trace (.pipeline entry i) =
      FMap.dom sb.patch ∪ FMap.dom sb.reads ∪ FMap.dom sb.writes)
    (whole : ∀ result, m.denotes p (Chunk.concat sb.input ⟨s, .eof⟩ hin) b.world.fs b.world.env result →
      ResultEquivalent memo.result result)
    (closing : ∃ result, m.denotes p ⟨s, .eof⟩ b.world.fs b.world.env result)
    (fold : ∀ result, m.denotes p ⟨s, .eof⟩ b.world.fs b.world.env result →
      m.denotes p (Chunk.concat sb.input ⟨s, .eof⟩ hin) b.world.fs b.world.env
        (combineResults (prefixResult sb) result hout))
    (avoid : Set sig.MTime) (finite : avoid.Finite) :
    ∃ tail patch reads writes, ClosingMatch pre b entry i p sb s memo hout tail patch reads writes ∧
      ∀ q file, FMap.get patch q = some (.write file) → file.mtime ∉ avoid := by
  obtain ⟨r, call⟩ := closing
  obtain ⟨patch, approx, fresh⟩ := commands.timestamps.fresh avoid finite r.patch
  let result : Result sig := { r with patch := patch }
  have denotes : m.denotes p ⟨s, .eof⟩ b.world.fs b.world.env result :=
    commands.timestamps.retimestamp p _ _ _ r call patch approx
  have equivalent := whole _ (fold result denotes)
  have fields := equivalent.1
  have status : result.status = some memo.ec := congrArg (fun x => x.1) fields
  have reads : sb.reads ⊎ result.reads = memo.reads := by
    have equal := congrArg (fun x => x.2.1) fields
    simpa [combineResults, prefixResult, Memo.result, empty,
      FMap.merge_empty_earlier, FMap.filterKeys_keys_empty] using equal
  have writes : sb.writes ⊎ result.writes = memo.writes := by
    have equal := congrArg (fun x => x.2.2.1) fields
    simpa [combineResults, prefixResult, Memo.result, empty,
      FMap.merge_empty_earlier, FMap.filterKeys_keys_empty] using equal
  have output : memo.output = Chunk.concat sb.output result.output hout :=
    (congrArg (fun x => x.2.2.2) fields).symm
  have patchEq : PatchApprox result.patch memo.patch := by
    simpa [combineResults, prefixResult, Memo.result, empty, FMap.merge_empty_earlier] using equivalent.2
  have eof : result.output.flag = .eof := (shape p _ _ _ result denotes).2 rfl |>.1
  have outEq : result.output = ⟨result.output.bytes, .eof⟩ := by
    cases value : result.output with
    | mk bytes flag =>
      have flagEq : flag = .eof := by simpa only [value] using eof
      subst flag
      rfl
  refine ⟨result.output.bytes, result.patch, result.reads, result.writes, ?_, ?_⟩
  · unfold ClosingMatch
    refine ⟨?_, ?_, patchEq, reads, writes, ?_, ?_⟩
    · have exactResult : result = ⟨some memo.ec, result.patch, result.reads, result.writes,
          ⟨result.output.bytes, .eof⟩⟩ := by
        generalize heq : result = rr at *
        cases rr with
        | mk exit patch reads writes output =>
          simp only at status outEq ⊢
          rw [status, ← outEq]
      rw [← exactResult]
      exact denotes
    · rw [← outEq]
      exact output
    · rw [patchEq.1]
    · rw [paths, empty, FMap.dom_empty, ← reads, ← writes, FMap.dom_merge_union, FMap.dom_merge_union, patchEq.1]
      ext q
      simp only [Set.mem_union, Set.mem_empty_iff_false, false_or]
      tauto
  · exact fresh

/-- E.7, over the post-selection domain and its stated local witness consistency. -/
theorem cache_hit_completion (shape : DenotationShape m) (commands : WellFormedCommands m)
    (host : HostWellFormed m h) (hash : HashInjective m)
    (pre : Prefix m h .live prog start) (operational : Operational pre) (ordered : ExitOrdered pre.trace)
    (cache : WellFormedCache m start.cache) (b : Boundary pre)
    (entry i : Nat) (p : sig.Probe) (sb : Sandbox sig) (s : Bytes) (key : Key sig) (memo : Memo sig)
    (selected : ∃ selection, b.selection? = some selection ∧ selection.head = .pipeline p i)
    (live : b.livePipeline entry i) (assigned : b.assigned entry i p) (cacheable : Cacheable m p)
    (slot : FMap.get b.world.sandbox i = some sb) (empty : sb.patch = ∅)
    (buffer : FMap.get b.world.buffer i = some ⟨s, .eof⟩)
    (hin : sb.input.flag = .open)
    (keyEquation : key = cacheKey m p b.world.env (Chunk.concat sb.input ⟨s, .eof⟩ hin))
    (lookup : FMap.get b.world.cache key = some memo) (valid : Valid m memo.reads memo.writes b.world.fs)
    (witness : FS sig) (certificate : EntryWitness m key memo witness)
    (consistent : TimestampConsistent ({recordOfFS witness} ∪ {recordOfFS b.world.fs})) :
    ∃ hout : sb.output.flag = .open, HitCompletion pre b entry i p sb s memo hout := by
  obtain ⟨selection, selectionAt, head⟩ := selected
  cases b with
  | final => simp [Boundary.selection?] at selectionAt
  | selected actual world allowed =>
    simp only [Boundary.selection?, Option.some.injEq] at selectionAt
    subst selection
    let boundary : Boundary pre := .selected actual world allowed
    have hout : sb.output.flag = .open := (Operational.liveOpenFlags shape host pre operational boundary entry i sb live slot).2
    obtain ⟨witnesses, chosen⟩ := WellFormedCache.exists_witnesses start.cache cache
    have preserved := prefixes_and_cache_preservation shape commands host hash pre operational ordered cache witnesses chosen boundary
    have entryPrefix := preserved.entries entry i p sb live assigned cacheable slot
    have paths := (live_buffer_properties host prog start pre operational boundary entry i sb live slot).accessPaths
    have memoCert : EntryWitness m (cacheKey m p world.env (Chunk.concat sb.input ⟨s, .eof⟩ hin)) memo witness := by
      simpa [boundary, Boundary.world, keyEquation] using certificate
    have memoValid : Valid m memo.reads memo.writes world.fs := by simpa [boundary, Boundary.world] using valid
    have localConsistency : TimestampConsistent ({recordOfFS witness} ∪ {recordOfFS world.fs}) := by
      simpa [boundary, Boundary.world] using consistent
    obtain ⟨wholeCall, wholeAgreement⟩ := validated_memo commands hash p world.env
      (Chunk.concat sb.input ⟨s, .eof⟩ hin) memo witness world.fs memoCert memoValid localConsistency
    have closing : ∃ result, m.denotes p ⟨s, .eof⟩ world.fs world.env result := by
      by_cases noHistory : openSteps pre.trace (.pipeline entry i) = []
      · have initial := (entryPrefix.zero noHistory).1
        refine ⟨memo.result, ?_⟩
        have bytes : sb.input.bytes = [] := congrArg (fun state => state.input.bytes) initial
        have inputEq : Chunk.concat sb.input ⟨s, .eof⟩ hin = ⟨s, .eof⟩ := by
          simp [Chunk.concat, bytes]
        simpa only [inputEq] using wholeCall
      · obtain ⟨env, first⟩ := entryPrefix.firstEnvironment noHistory
        have envEq : world.env = env := FirstEnvironment.boundary_env host pre operational actual world allowed
          entry i p head live env first
        obtain ⟨repair, repaired⟩ := entryPrefix.progressed noHistory env first
        have repairEmpty : repair = ∅ := by
          apply FMap.eq_empty_of_dom_eq_empty
          rw [repaired.domain, empty, FMap.dom_empty]
        subst repair
        have prefixCall : m.denotes p sb.input world.fs world.env (prefixResult sb) := by
          simpa only [boundary, Boundary.world, applyPatch_empty, envEq] using repaired.denotation
        have finish := commands.completion p cacheable world.env world.fs sb.input s (prefixResult sb) memo.result
          hin rfl hout memo.output_eof prefixCall wholeCall
        simpa only [prefixResult, empty, applyPatch_empty] using finish
    have fold : ∀ result, m.denotes p ⟨s, .eof⟩ world.fs world.env result →
        m.denotes p (Chunk.concat sb.input ⟨s, .eof⟩ hin) world.fs world.env
          (combineResults (prefixResult sb) result hout) := by
      intro result call
      by_cases noHistory : openSteps pre.trace (.pipeline entry i) = []
      · have initial := (entryPrefix.zero noHistory).1
        have initialFold := EntryFold.initial (m := m) p sb.base world.fs world.env
        rw [← initial] at initialFold
        exact initialFold _ _ call hin hout
      · obtain ⟨env, first⟩ := entryPrefix.firstEnvironment noHistory
        have envEq : world.env = env := FirstEnvironment.boundary_env host pre operational actual world allowed
          entry i p head live env first
        obtain ⟨repair, repaired⟩ := entryPrefix.progressed noHistory env first
        have repairEmpty : repair = ∅ := by
          apply FMap.eq_empty_of_dom_eq_empty
          rw [repaired.domain, empty, FMap.dom_empty]
        subst repair
        have entryFold : EntryFold (m := m) p sb world.fs world.fs world.env := by
          simpa only [boundary, Boundary.world, applyPatch_empty, envEq] using repaired.fold
        exact entryFold _ _ call hin hout
    have fresh : ∀ avoid : Set sig.MTime, avoid.Finite → ∃ tail patch reads writes,
        ClosingMatch pre boundary entry i p sb s memo hout tail patch reads writes ∧
          ∀ q file, FMap.get patch q = some (.write file) → file.mtime ∉ avoid := by
      intro avoid finite
      apply closingMatch_of_fold shape commands pre boundary entry i p sb s memo hin hout empty paths
      · simpa only [boundary, Boundary.world] using wholeAgreement
      · simpa only [boundary, Boundary.world] using closing
      · simpa only [boundary, Boundary.world] using fold
      · exact finite
    refine ⟨hout, ?_, fresh⟩
    obtain ⟨tail, patch, reads, writes, matched, _⟩ := fresh ∅ Set.finite_empty
    exact ⟨tail, patch, reads, writes, matched⟩

end
end IncrPP
end Incr
