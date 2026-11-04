import Incr.IncrPP.Bisimulation.ProbeMatching
import Incr.IncrPP.Bisimulation.Witnesses

/-!
# Matching an actual live cache hit

The local witness comes from E.10. The closing call comes from E.7 and
uses the actual selected environment and consumed EOF chunk.
-/

namespace Incr.IncrPP

noncomputable section

variable {sig : Signature} {m : CommandModel sig} {h : Host sig}
  {prog : sig.Prog} {start : World sig}

/-- E.10 supplies the local consistency premise needed by memo validation and E.7. -/
theorem selected_memo_local_witness (shape : DenotationShape m) (commands : WellFormedCommands m)
    (host : HostWellFormed m h) (hash : HashInjective m)
    (context : PrefixContext m h prog start) (pre : Prefix m h .live prog start)
    (admissible : Admissible context.witnesses pre) (b : Boundary pre)
    (key : Key sig) (memo : Memo sig) (lookup : FMap.get b.world.cache key = some memo) :
    ∃ fs, EntryWitness m key memo fs ∧ TimestampConsistent ({recordOfFS fs} ∪ {recordOfFS b.world.fs}) := by
  obtain ⟨fs, certificate, consistent⟩ := witness_consistency shape commands host hash context pre admissible b key memo lookup
  refine ⟨fs, certificate, ?_⟩
  apply (two_filesystems_consistent_iff fs b.world.fs).mpr
  apply TimestampCompatible.mono ?_ ((b.paperRecords_witness_consistent_iff context.witnesses fs).mp consistent)
  intro record member
  rcases List.mem_append.mp member with fromWitness | fromWorld
  · exact List.mem_append_left _ (List.mem_append_left _ fromWitness)
  · rcases record with ⟨q, file⟩
    have found := get_of_mem_fsRecords fromWorld
    exact List.mem_append_left _ (List.mem_append_right _ (Boundary.fs_record pre b q file found))

/-- Two partial concatenations with the same left chunk and EOF flag have the same tail bytes. -/
theorem concat_eof_tail_unique (left : Chunk) (openFlag : left.flag = .open) (a b : Bytes)
    (equal : Chunk.concat left ⟨a, .eof⟩ openFlag = Chunk.concat left ⟨b, .eof⟩ openFlag) : a = b := by
  have bytes := congrArg Chunk.bytes equal
  exact List.append_cancel_left bytes

/-- An actual pipeline hit has the matching suffix call and both exact cumulative path equations. -/
theorem pipeline_hit_closing (shape : DenotationShape m) (commands : WellFormedCommands m)
    (host : HostWellFormed m h) (hash : HashInjective m)
    (context : PrefixContext m h prog start) (pre : Prefix m h .live prog start)
    (admissible : Admissible context.witnesses pre)
    (selection : Selection sig) (world : World sig) (allowed : h.select prog pre.final selection world)
    (entry i : Nat) (p : sig.Probe) (sb : Sandbox sig) (s tail : Bytes) (memo : Memo sig)
    (head : selection.head = .pipeline p i)
    (live : (Boundary.selected selection world allowed).livePipeline entry i)
    (assigned : (Boundary.selected selection world allowed).assigned entry i p)
    (cacheable : Cacheable m p) (slot : FMap.get world.sandbox i = some sb) (empty : sb.patch = ∅)
    (buffer : FMap.get world.buffer i = some ⟨s, .eof⟩)
    (hin : sb.input.flag = .open) (hout : sb.output.flag = .open)
    (lookup : FMap.get world.cache (cacheKey m p world.env (Chunk.concat sb.input ⟨s, .eof⟩ hin)) = some memo)
    (valid : Valid m memo.reads memo.writes world.fs)
    (guard : memo.output = Chunk.concat sb.output ⟨tail, .eof⟩ hout) :
    ∃ patch reads writes,
      m.denotes p ⟨s, .eof⟩ world.fs world.env ⟨some memo.ec, patch, reads, writes, ⟨tail, .eof⟩⟩ ∧
      PatchApprox patch memo.patch ∧ sb.reads ⊎ reads = memo.reads ∧ sb.writes ⊎ writes = memo.writes ∧
      (componentWrites pre.trace (.pipeline entry i) ∪ FMap.dom memo.patch =
        componentWrites pre.trace (.pipeline entry i) ∪ FMap.dom patch) ∧
      (componentAccesses pre.trace (.pipeline entry i) ∪
        (FMap.dom memo.patch ∪ FMap.dom memo.reads ∪ FMap.dom memo.writes) =
        componentAccesses pre.trace (.pipeline entry i) ∪
        (FMap.dom patch ∪ FMap.dom reads ∪ FMap.dom writes)) := by
  let b : Boundary pre := .selected selection world allowed
  let key := cacheKey m p world.env (Chunk.concat sb.input ⟨s, .eof⟩ hin)
  obtain ⟨fs, certificate, consistent⟩ := selected_memo_local_witness shape commands host hash
    context pre admissible b key memo lookup
  obtain ⟨outputOpen, completion⟩ := cache_hit_completion shape commands host hash pre admissible.operational
    admissible.ordered context.cache b entry i p sb s key memo ⟨selection, rfl, head⟩ live assigned cacheable
    slot empty buffer hin rfl lookup valid fs certificate consistent
  obtain ⟨actualTail, patch, reads, writes, matched⟩ := completion.closing
  rcases matched with ⟨call, output, approx, readsEq, writesEq, writePaths, accessPaths⟩
  have equalTails : actualTail = tail := concat_eof_tail_unique sb.output hout actualTail tail (output.symm.trans guard)
  subst actualTail
  exact ⟨patch, reads, writes, call, approx, readsEq, writesEq, writePaths, accessPaths⟩

/-- An actual standalone hit denotes its complete memo result on the selected live filesystem. -/
theorem standalone_hit_call (shape : DenotationShape m) (commands : WellFormedCommands m)
    (host : HostWellFormed m h) (hash : HashInjective m)
    (context : PrefixContext m h prog start) (pre : Prefix m h .live prog start)
    (admissible : Admissible context.witnesses pre) (selection : Selection sig) (world : World sig)
    (allowed : h.select prog pre.final selection world) (p : sig.Probe) (s : Bytes) (memo : Memo sig)
    (lookup : FMap.get world.cache (cacheKey m p world.env ⟨s, .eof⟩) = some memo)
    (valid : Valid m memo.reads memo.writes world.fs) :
    m.denotes p ⟨s, .eof⟩ world.fs world.env memo.result := by
  let b : Boundary pre := .selected selection world allowed
  obtain ⟨fs, certificate, consistent⟩ := selected_memo_local_witness shape commands host hash
    context pre admissible b (cacheKey m p world.env ⟨s, .eof⟩) memo lookup
  exact (validated_memo commands hash p world.env ⟨s, .eof⟩ memo fs world.fs certificate valid consistent).1

/-- A live pipeline hit has a fresh vanilla close with the same effect and cumulative paths. -/
theorem pipeline_hit_match (shape : DenotationShape m) (commands : WellFormedCommands m)
    (host : HostWellFormed m h) (hash : HashInjective m)
    (context : PrefixContext m h prog start) (pre : Prefix m h .live prog start)
    (admissible : Admissible context.witnesses pre)
    (selection : Selection sig) (world vanilla : World sig) (allowed : h.select prog pre.final selection world)
    (entry i : Nat) (p : sig.Probe) (sb : Sandbox sig) (s tail : Bytes) (memo : Memo sig)
    (applied : Patch sig) (buffers : FMap Nat Chunk) (out : Option Chunk)
    (head : selection.head = .pipeline p i) (control : ControlAgree world vanilla)
    (agreement : FSApprox world.fs vanilla.fs)
    (live : (Boundary.selected selection world allowed).livePipeline entry i)
    (assigned : (Boundary.selected selection world allowed).assigned entry i p)
    (cacheable : Cacheable m p) (empty : sb.patch = ∅)
    (buffer : FMap.get world.buffer i = some ⟨s, .eof⟩)
    (slot : FMap.get world.sandbox i = some sb)
    (hin : sb.input.flag = .open) (hout : sb.output.flag = .open)
    (lookup : FMap.get world.cache (cacheKey m p world.env (Chunk.concat sb.input ⟨s, .eof⟩ hin)) = some memo)
    (valid : Valid m memo.reads memo.writes world.fs)
    (guard : memo.output = Chunk.concat sb.output ⟨tail, .eof⟩ hout)
    (appliedApprox : PatchApprox applied memo.patch)
    (routed : put (world.buffer ∖ i) i ⟨tail, .eof⟩ = some (buffers, out))
    (records : Records sig) :
    ∃ vafter, ∃ vd : VanillaDerivation m vanilla (.pipeline p i) vafter out,
      ControlAgree (closeWorld world i memo.ec applied buffers) vafter ∧
      VanillaDerivation.input vd = ⟨s, .eof⟩ ∧
      (VanillaDerivation.result vd).output = ⟨tail, .eof⟩ ∧
      PatchApprox (VanillaDerivation.result vd).patch applied ∧
      FSApprox (closeWorld world i memo.ec applied buffers).fs vafter.fs ∧
      (componentWrites pre.trace (.pipeline entry i) ∪ FMap.dom memo.patch =
        componentWrites pre.trace (.pipeline entry i) ∪ FMap.dom (VanillaDerivation.result vd).patch) ∧
      (componentAccesses pre.trace (.pipeline entry i) ∪
        (FMap.dom memo.patch ∪ FMap.dom memo.reads ∪ FMap.dom memo.writes) =
        componentAccesses pre.trace (.pipeline entry i) ∪
        (FMap.dom (VanillaDerivation.result vd).patch ∪ FMap.dom (VanillaDerivation.result vd).reads ∪
          FMap.dom (VanillaDerivation.result vd).writes)) ∧
      FreshPatch (VanillaDerivation.result vd).patch vanilla.fs vanilla.fs ∧
      ∀ q file, FMap.get (VanillaDerivation.result vd).patch q = some (.write file) →
        ∀ q' old, (q', old) ∈ records → file.mtime ≠ old.mtime := by
  obtain ⟨patch, reads, writes, closing, patchMemo, readsEq, writesEq, writePaths, accessPaths⟩ :=
    pipeline_hit_closing shape commands host hash context pre admissible selection world allowed entry i p sb s tail memo
      head live assigned cacheable slot empty buffer hin hout lookup valid guard
  let closingResult : Result sig := ⟨some memo.ec, patch, reads, writes, ⟨tail, .eof⟩⟩
  obtain ⟨r, call, status, output, targetWrites, targetReads, targetPatch, fresh, outside⟩ :=
    transport_call_fresh commands p ⟨s, .eof⟩ world.fs vanilla.fs vanilla.fs world.env closingResult
      closing agreement records
  have targetCall : m.denotes p ⟨s, .eof⟩ vanilla.fs vanilla.env r := by
    simpa only [control.2.2.1] using call
  let source : LiveDerivation m world (.pipeline p i) (closeWorld world i memo.ec applied buffers) out :=
    .cacheCloseHit world p i sb s tail memo applied buffers out cacheable empty buffer slot hin hout lookup
    ((useCache_iff_of_get lookup).mpr valid) guard
      appliedApprox routed
  obtain ⟨vafter, vd, afterControl, inputEq, resultEq⟩ :=
    source.to_vanilla control r targetCall status output
  have vdEffects := vd.executing_effects
  have patchApplied : PatchApprox r.patch applied := patchApprox_trans (patchApprox_trans targetPatch patchMemo)
    (patchApprox_symm appliedApprox)
  refine ⟨vafter, vd, afterControl, inputEq, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [resultEq] using output
  · simpa only [resultEq] using patchApplied
  · change FSApprox (applyPatch world.fs applied) vafter.fs
    rw [vdEffects.2, resultEq]
    exact fsApprox_applyPatch agreement (patchApprox_symm patchApplied)
  · simpa only [resultEq, targetPatch.1] using writePaths
  · simpa only [resultEq, targetPatch.1, targetReads, targetWrites] using accessPaths
  · simpa only [resultEq] using fresh
  · simpa only [resultEq] using outside

/-- A live standalone hit has a fresh vanilla match with the memo's actual effect domains. -/
theorem standalone_hit_match (shape : DenotationShape m) (commands : WellFormedCommands m)
    (host : HostWellFormed m h) (hash : HashInjective m)
    (context : PrefixContext m h prog start) (pre : Prefix m h .live prog start)
    (admissible : Admissible context.witnesses pre)
    (selection : Selection sig) (world vanilla : World sig) (allowed : h.select prog pre.final selection world)
    (p : sig.Probe) (s : Bytes) (memo : Memo sig) (applied : Patch sig)
    (control : ControlAgree world vanilla) (agreement : FSApprox world.fs vanilla.fs)
    (cacheable : Cacheable m p) (stdin : world.stdin = ⟨s, .eof⟩)
    (lookup : FMap.get world.cache (cacheKey m p world.env ⟨s, .eof⟩) = some memo)
    (valid : Valid m memo.reads memo.writes world.fs) (appliedApprox : PatchApprox applied memo.patch)
    (records : Records sig) :
    ∃ vafter, ∃ vd : VanillaDerivation m vanilla (.standalone p) vafter (some memo.output),
      ControlAgree (standaloneWorld world memo.ec applied) vafter ∧
      VanillaDerivation.input vd = ⟨s, .eof⟩ ∧
      (VanillaDerivation.result vd).output = memo.output ∧
      PatchApprox (VanillaDerivation.result vd).patch applied ∧
      FMap.dom (VanillaDerivation.result vd).reads = FMap.dom memo.reads ∧
      (VanillaDerivation.result vd).writes = memo.writes ∧
      FSApprox (standaloneWorld world memo.ec applied).fs vafter.fs ∧
      FreshPatch (VanillaDerivation.result vd).patch vanilla.fs vanilla.fs ∧
      ∀ q file, FMap.get (VanillaDerivation.result vd).patch q = some (.write file) →
        ∀ q' old, (q', old) ∈ records → file.mtime ≠ old.mtime := by
  have sourceCall := standalone_hit_call shape commands host hash context pre admissible selection world allowed
    p s memo lookup valid
  obtain ⟨r, call, status, output, targetWrites, targetReads, targetPatch, fresh, outside⟩ :=
    transport_call_fresh commands p ⟨s, .eof⟩ world.fs vanilla.fs vanilla.fs world.env memo.result
      sourceCall agreement records
  have targetCall : m.denotes p ⟨s, .eof⟩ vanilla.fs vanilla.env r := by
    simpa only [control.2.2.1] using call
  let source : LiveDerivation m world (.standalone p) (standaloneWorld world memo.ec applied) (some memo.output) :=
    .cacheStandaloneHit world p s memo applied cacheable stdin lookup valid appliedApprox
  obtain ⟨vafter, vd, afterControl, inputEq, resultEq⟩ := source.to_vanilla control r targetCall status output
  have vdEffects := vd.executing_effects
  have patchApplied : PatchApprox r.patch applied := patchApprox_trans targetPatch (patchApprox_symm appliedApprox)
  refine ⟨vafter, vd, afterControl, inputEq, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [resultEq, Memo.result] using output
  · simpa only [resultEq] using patchApplied
  · simpa only [resultEq, Memo.result] using targetReads
  · simpa only [resultEq, Memo.result] using targetWrites
  · change FSApprox (applyPatch world.fs applied) vafter.fs
    rw [vdEffects.2, resultEq]
    exact fsApprox_applyPatch agreement (patchApprox_symm patchApplied)
  · simpa only [resultEq] using fresh
  · simpa only [resultEq] using outside

end
end IncrPP
end Incr
