import Incr.IncrPP.Bisimulation.MatchingOrder

/-!
# Retained cache-hit cases for E.11

These facts expose only witnesses already present in the independent raw
live derivation. They do not assume a synthetic hit step.
-/

namespace Incr.IncrPP

noncomputable section

variable {sig : Signature} {m : CommandModel sig}

/-- A pipeline hit retains all data needed to replay its actual suffix. -/
def PipelineHitFacts {w after : World sig} {head : Head sig} {out : Option Chunk}
    (d : LiveDerivation m w head after out) : Prop :=
  ∃ (p : sig.Probe) (i : Nat) (sb : Sandbox sig) (s tail : Bytes) (memo : Memo sig)
    (applied : Patch sig) (buffers : FMap Nat Chunk),
    ∃ (hin : sb.input.flag = .open) (hout : sb.output.flag = .open),
      head = .pipeline p i ∧ LiveDerivation.input d = ⟨s, .eof⟩ ∧ LiveDerivation.result d = memo.result ∧
      after = closeWorld w i memo.ec applied buffers ∧ Cacheable m p ∧ sb.patch = ∅ ∧
      FMap.get w.buffer i = some ⟨s, .eof⟩ ∧ FMap.get w.sandbox i = some sb ∧
      FMap.get w.cache (cacheKey m p w.env (Chunk.concat sb.input ⟨s, .eof⟩ hin)) = some memo ∧
      Valid m memo.reads memo.writes w.fs ∧ memo.output = Chunk.concat sb.output ⟨tail, .eof⟩ hout ∧
      PatchApprox applied memo.patch ∧ put (w.buffer ∖ i) i ⟨tail, .eof⟩ = some (buffers, out)

/-- A standalone hit retains its whole-input memo and actual replay patch. -/
def StandaloneHitFacts {w after : World sig} {head : Head sig} {out : Option Chunk}
    (d : LiveDerivation m w head after out) : Prop :=
  ∃ (p : sig.Probe) (s : Bytes) (memo : Memo sig) (applied : Patch sig),
      head = .standalone p ∧ LiveDerivation.input d = ⟨s, .eof⟩ ∧ LiveDerivation.result d = memo.result ∧
      after = standaloneWorld w memo.ec applied ∧ out = some memo.output ∧ Cacheable m p ∧
      w.stdin = ⟨s, .eof⟩ ∧ FMap.get w.cache (cacheKey m p w.env ⟨s, .eof⟩) = some memo ∧
      Valid m memo.reads memo.writes w.fs ∧ PatchApprox applied memo.patch

/-- Every executing live call uses its actual selected filesystem. -/
theorem LiveDerivation.callFS_some {w after : World sig} {head : Head sig} {out : Option Chunk}
    (d : LiveDerivation m w head after out) {fs : FS sig} (call : LiveDerivation.callFS d = some fs) : fs = w.fs := by
  cases d <;> simp_all [LiveDerivation.callFS]

/-- A nonexecuting live rule is exactly one of the two actual cache-hit branches. -/
theorem LiveDerivation.hit_cases {w after : World sig} {head : Head sig} {out : Option Chunk}
    (d : LiveDerivation m w head after out) (hit : LiveDerivation.callFS d = none) :
    PipelineHitFacts d ∨ StandaloneHitFacts d := by
  cases d
  all_goals simp only [LiveDerivation.callFS] at hit
  all_goals try contradiction
  case cacheCloseHit =>
    left
    refine ⟨_, _, _, _, _, _, _, _, _, _, rfl, rfl, rfl, rfl,
      by assumption, by assumption, by assumption, by assumption, by assumption,
      (useCache_iff_of_get (by assumption)).mp (by assumption),
      by assumption, by assumption, by assumption⟩
  case cacheStandaloneHit =>
    right
    refine ⟨_, _, _, _, rfl, rfl, rfl, rfl, rfl, by assumption,
      by assumption, by assumption, by assumption, by assumption⟩

variable {h : Host sig} {prog : sig.Prog} {start : World sig}

/-- An operationally fresh vanilla candidate with matching paths assembles an admitted E.9 successor. -/
theorem Correspondence.forward_finish (shape : DenotationShape m) (commands : WellFormedCommands m)
    (host : HostWellFormed m h) (hash : HashInjective m) {context : PrefixContext m h prog start}
    {live live' : Prefix m h .live prog start} {vanilla : Prefix m h .vanilla prog start}
    (related : Correspondence context live vanilla)
    (left : StepDerivation m h .live prog) (right : StepDerivation m h .vanilla prog)
    (leftTrace : live'.trace = live.trace ++ [left]) (leftAfter : live'.final = left.after)
    (leftAdmissible : Admissible context.witnesses live') (rightBefore : right.before = vanilla.final)
    (matched : MatchingProbeSteps left right) (afterControl : ControlAgree left.after right.after)
    (afterFS : FSApprox left.after.fs right.after.fs)
    (paths : PathsAtEveryPrefix (live.trace ++ [left]) (vanilla.trace ++ [right]))
    (freshLocal : FreshPatch (VanillaDerivation.result right.probe).patch right.selected.fs right.selected.fs)
    (freshRecords : ∀ q file, FMap.get (VanillaDerivation.result right.probe).patch q = some (.write file) →
      ∀ q' old, (q', old) ∈ vanilla.records ++ witnessRecords context.witnesses → file.mtime ≠ old.mtime) :
    ∃ vanilla' : Prefix m h .vanilla prog start,
      PrefixStep context.witnesses left.selection.head vanilla vanilla' ∧ Correspondence context live' vanilla' := by
  let vanilla' : Prefix m h .vanilla prog start :=
    ⟨vanilla.trace ++ [right], right.after, vanilla.initial,
      (Connected.snoc_iff vanilla.trace right start right.after).mpr ⟨by simpa [rightBefore] using vanilla.connected, rfl⟩⟩
  have timestamp := Operational.vanilla_snoc_fresh host vanilla vanilla' related.vanillaAdmissible.operational
    context.witnesses related.vanillaAdmissible.normalizedWitnesses right rightBefore rfl freshLocal freshRecords
  have fullMatched : List.Forall₂ MatchingProbeSteps live'.trace vanilla'.trace := by
    rw [leftTrace]
    exact List.rel_append related.matchingSteps (List.Forall₂.cons matched List.Forall₂.nil)
  have fullPaths : PathsAtEveryPrefix live'.trace vanilla'.trace := by simpa only [leftTrace, vanilla'] using paths
  have ordered := (matching_exitOrdered fullMatched fullPaths).mp leftAdmissible.ordered
  have rightAdmissible : Admissible context.witnesses vanilla' :=
    ⟨timestamp.1, ordered, (vanilla'.paperRecords_witness_consistent_iff context.witnesses).mpr timestamp.2⟩
  have control : ControlAgree live'.final vanilla'.final := by simpa only [leftAfter, vanilla'] using afterControl
  have fs : FSApprox live'.final.fs vanilla'.final.fs := by simpa only [leftAfter, vanilla'] using afterFS
  have correspondence := related.snoc shape commands host hash left right leftTrace rfl matched leftAdmissible
    rightAdmissible control fs fullPaths
  exact ⟨vanilla', ⟨related.vanillaAdmissible, rightAdmissible, right, rightBefore, matched.1.symm, rfl, rfl⟩,
    correspondence⟩

/-- Reindexing a vanilla derivation by equal returned output preserves its result. -/
theorem VanillaDerivation.result_output_cast {before after : World sig} {head : Head sig}
    {left right : Option Chunk} (equal : left = right) (d : VanillaDerivation m before head after left) :
    VanillaDerivation.result (equal ▸ d) = VanillaDerivation.result d := by
  cases equal
  rfl

/-- An actual live cache-hit edge has a fresh admitted vanilla edge preserving E.9. -/
theorem Correspondence.forward_hit (shape : DenotationShape m) (commands : WellFormedCommands m)
    (host : HostWellFormed m h) (hash : HashInjective m) {context : PrefixContext m h prog start}
    {live live' : Prefix m h .live prog start} {vanilla : Prefix m h .vanilla prog start}
    (related : Correspondence context live vanilla) (control : ControlAgree live.final vanilla.final)
    (d : StepDerivation m h .live prog) (before : d.before = live.final)
    (joined : live'.trace = live.trace ++ [d]) (after : live'.final = d.after)
    (liveAdmissible : Admissible context.witnesses live') (hit : LiveDerivation.callFS d.probe = none) :
    ∃ vanilla' : Prefix m h .vanilla prog start,
      PrefixStep context.witnesses d.selection.head vanilla vanilla' ∧ Correspondence context live' vanilla' := by
  have allowed : h.select prog live.final d.selection d.selected := by simpa only [before] using d.host
  obtain ⟨selection, world, chosen, matched⟩ :=
    (related.selection_transport host control).1 d.selection d.selected allowed
  have selectedPair := related.selected_pair host control d.selection d.selected allowed selection world chosen matched
  rcases d.probe.hit_cases hit with pipeline | standalone
  · obtain ⟨p, i, sb, s, tail, memo, applied, buffers, hin, hout, head, inputEq, resultEq,
      sourceAfter, cacheable, empty, buffer, slot, lookup, valid, guard, appliedApprox, routed⟩ := pipeline
    obtain ⟨entry, liveEntry, assigned⟩ := Boundary.selected_pipeline_live host live
      related.liveAdmissible.operational d allowed head sb slot
    obtain ⟨vafter, vd, afterControl, targetInput, targetOutput, targetPatch, fsEq,
      writePaths, accessPaths, freshLocal, freshRecords⟩ :=
      pipeline_hit_match shape commands host hash context live related.liveAdmissible d.selection d.selected world allowed
        entry i p sb s tail memo applied buffers d.out head selectedPair.1 selectedPair.2 liveEntry assigned
        cacheable empty buffer slot hin hout lookup valid guard appliedApprox routed
        (vanilla.records ++ witnessRecords context.witnesses)
    have indexEq : Head.pipeline p i = selection.head := head.symm.trans matched.1
    let targetProbe : VanillaDerivation m world selection.head vafter d.out := indexEq ▸ vd
    have targetResult : VanillaDerivation.result targetProbe = VanillaDerivation.result vd :=
      VanillaDerivation.result_head_cast indexEq vd
    let target : StepDerivation m h .vanilla prog :=
      ⟨vanilla.final, selection, world, vafter, d.out, chosen, targetProbe⟩
    have matchedStep : MatchingProbeSteps d target := by
      refine ⟨matched.1, rfl, selectedPair.1, ?_, matched.2.1⟩
      simpa only [sourceAfter, target] using afterControl
    have sourceComponent : componentAt (live.trace ++ [d]) live.trace.length d = some (.pipeline entry i) := by
      rw [Boundary.componentAt_selected live d allowed head, liveEntry.1]
      rfl
    have pathMatch : PathsAtEveryPrefix (live.trace ++ [d]) (vanilla.trace ++ [target]) := by
      apply related.paths_snoc_hit host d target matchedStep entry i sourceComponent
      · simpa only [ProbeDerivation.result, target, targetResult, resultEq, Memo.result] using writePaths
      · simpa only [StepDerivation.accesses, ProbeDerivation.result, target, targetResult, resultEq, Memo.result] using accessPaths
    apply related.forward_finish shape commands host hash d target joined after liveAdmissible rfl matchedStep
    · simpa only [sourceAfter, target] using afterControl
    · simpa only [sourceAfter, target] using fsEq
    · exact pathMatch
    · simpa only [target, targetResult] using freshLocal
    · simpa only [target, targetResult] using freshRecords
  · obtain ⟨p, s, memo, applied, head, inputEq, resultEq, sourceAfter, sourceOut,
      cacheable, stdin, lookup, valid, appliedApprox⟩ := standalone
    obtain ⟨vafter, vd, afterControl, targetInput, targetOutput, targetPatch, readsEq, writesEq,
      fsEq, freshLocal, freshRecords⟩ :=
      standalone_hit_match shape commands host hash context live related.liveAdmissible d.selection d.selected world allowed
        p s memo applied selectedPair.1 selectedPair.2 cacheable stdin lookup valid appliedApprox
        (vanilla.records ++ witnessRecords context.witnesses)
    have indexEq : Head.standalone p = selection.head := head.symm.trans matched.1
    let targetProbe : VanillaDerivation m world selection.head vafter d.out := sourceOut.symm ▸ (indexEq ▸ vd)
    have targetResult : VanillaDerivation.result targetProbe = VanillaDerivation.result vd :=
      (VanillaDerivation.result_output_cast sourceOut.symm (indexEq ▸ vd)).trans
        (VanillaDerivation.result_head_cast indexEq vd)
    let target : StepDerivation m h .vanilla prog :=
      ⟨vanilla.final, selection, world, vafter, d.out, chosen, targetProbe⟩
    have matchedStep : MatchingProbeSteps d target := by
      refine ⟨matched.1, rfl, selectedPair.1, ?_, matched.2.1⟩
      simpa only [sourceAfter, target] using afterControl
    have pathMatch : PathsAtEveryPrefix (live.trace ++ [d]) (vanilla.trace ++ [target]) := by
      apply related.paths_snoc_equal_effects host d target matchedStep
      · simpa only [ProbeDerivation.result, target, targetResult, resultEq, Memo.result] using
          (patchApprox_trans targetPatch appliedApprox).1.symm
      · simpa only [ProbeDerivation.result, target, targetResult, resultEq, Memo.result] using readsEq.symm
      · simpa only [ProbeDerivation.result, target, targetResult, resultEq, Memo.result] using congrArg FMap.dom writesEq.symm
    apply related.forward_finish shape commands host hash d target joined after liveAdmissible rfl matchedStep
    · simpa only [sourceAfter, target] using afterControl
    · simpa only [sourceAfter, target] using fsEq
    · exact pathMatch
    · simpa only [target, targetResult] using freshLocal
    · simpa only [target, targetResult] using freshRecords

end
end IncrPP
end Incr
