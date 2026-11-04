import Incr.IncrPP.Bisimulation.MatchingObservations

/-!
# Produced-output observations for the distinct main theorem

Output equality follows from actual routing effects or the returned chunk.
It does not identify external supply annotations.
-/

namespace Incr.IncrPP

noncomputable section

variable {sig : Signature} {m : CommandModel sig} {h : Host sig} {prog : sig.Prog}

/-- Each pipeline rule routes its actual produced output to the selected successor. -/
theorem ProbeDerivation.pipeline_routing {executor : Executor} {before after : World sig}
    {p : sig.Probe} {slot : Nat} {returned : Option Chunk}
    (d : ProbeDerivation m executor before (.pipeline p slot) after returned) :
    ∃ buffers, put buffers slot (ProbeDerivation.produced d) = some (after.buffer, returned) ∧
      FMap.get buffers (slot + 1) = FMap.get before.buffer (slot + 1) := by
  cases executor <;> cases d <;>
    simp only [ProbeDerivation.produced, LiveDerivation.produced, VanillaDerivation.produced, closeWorld]
  all_goals first
    | (refine ⟨_, by assumption, ?_⟩; exact FMap.get_set_other (by omega))
    | (refine ⟨_, by assumption, ?_⟩; exact FMap.get_erase_of_ne (by omega))

/-- A standalone rule returns exactly its actual produced output. -/
theorem ProbeDerivation.standalone_returned {executor : Executor} {before after : World sig}
    {p : sig.Probe} {returned : Option Chunk}
    (d : ProbeDerivation m executor before (.standalone p) after returned) :
    returned = some (ProbeDerivation.produced d) := by
  cases executor <;> cases d <;> rfl

/-- Equal successor inputs and outputs make successful routing's produced chunks equal. -/
theorem put_produced_unique {left right leftAfter rightAfter : FMap Nat Chunk} {slot : Nat}
    {leftOut rightOut : Chunk} {returned : Option Chunk}
    (leftPut : put left slot leftOut = some (leftAfter, returned))
    (rightPut : put right slot rightOut = some (rightAfter, returned))
    (successor : FMap.get left (slot + 1) = FMap.get right (slot + 1))
    (after : FMap.get leftAfter (slot + 1) = FMap.get rightAfter (slot + 1)) : leftOut = rightOut := by
  unfold put at leftPut rightPut
  cases next : FMap.get left (slot + 1) with
  | none =>
    have other : FMap.get right (slot + 1) = none := successor.symm.trans next
    simp only [next, Option.some.injEq, Prod.mk.injEq] at leftPut
    simp only [other, Option.some.injEq, Prod.mk.injEq] at rightPut
    exact Option.some.inj (leftPut.2.trans rightPut.2.symm)
  | some chunk =>
    have other : FMap.get right (slot + 1) = some chunk := successor.symm.trans next
    cases chunk with
    | mk bytes flag =>
      cases flag with
      | eof => simp [next] at leftPut
      | «open» =>
        simp only [next, Option.some.injEq, Prod.mk.injEq] at leftPut
        simp only [other, Option.some.injEq, Prod.mk.injEq] at rightPut
        obtain ⟨rfl, _⟩ := leftPut
        obtain ⟨rfl, _⟩ := rightPut
        simp only [FMap.get_set_self, Option.some.injEq, Chunk.mk.injEq] at after
        cases leftOut
        cases rightOut
        simp only at after ⊢
        have bytesEq := List.append_cancel_left after.1
        cases bytesEq
        cases after.2
        rfl

/-- Matched raw probes with equal controls and returned chunks produce equal chunks. -/
theorem matched_probe_produced {wl wr al ar : World sig} {head : Head sig} {returned : Option Chunk}
    (dl : ProbeDerivation m .live wl head al returned)
    (dr : ProbeDerivation m .vanilla wr head ar returned)
    (selected : ControlAgree wl wr) (after : ControlAgree al ar) :
    ProbeDerivation.produced dl = ProbeDerivation.produced dr := by
  cases head with
  | standalone p =>
    exact Option.some.inj ((ProbeDerivation.standalone_returned dl).symm.trans
      (ProbeDerivation.standalone_returned dr))
  | pipeline p i =>
    obtain ⟨lb, lp, ls⟩ := ProbeDerivation.pipeline_routing dl
    obtain ⟨rb, rp, rs⟩ := ProbeDerivation.pipeline_routing dr
    apply put_produced_unique lp rp
    · rw [ls, rs, selected.2.2.2.1]
    · rw [after.2.2.2.1]

/-- Matched retained steps have equal produced chunks as well as equal returned chunks. -/
theorem MatchingProbeSteps.produced {live : StepDerivation m h .live prog}
    {vanilla : StepDerivation m h .vanilla prog} (matched : MatchingProbeSteps live vanilla) :
    ProbeDerivation.produced live.probe = ProbeDerivation.produced vanilla.probe := by
  rcases live with ⟨bl, sl, wl, al, ol, hostl, dl⟩
  rcases vanilla with ⟨br, sr, wr, ar, or, hostr, dr⟩
  obtain ⟨head, returned, selected, after, _⟩ := matched
  dsimp only at head returned selected after ⊢
  cases sl with
  | mk hl il dlv =>
    cases sr with
    | mk hr ir drv =>
      dsimp only at head
      cases head
      cases returned
      exact matched_probe_produced dl dr selected after

/-- Matching trace lists have equal produced and returned chunk lists. -/
theorem matching_produced_returned {live : Trace m h .live prog} {vanilla : Trace m h .vanilla prog}
    (matched : List.Forall₂ MatchingProbeSteps live vanilla) :
    live.map (fun d => ProbeDerivation.produced d.probe) = vanilla.map (fun d => ProbeDerivation.produced d.probe) ∧
      live.map (fun d => d.out) = vanilla.map (fun d => d.out) := by
  induction matched with
  | nil => exact ⟨rfl, rfl⟩
  | cons step rest ih =>
    exact ⟨congrArg₂ List.cons step.produced ih.1, congrArg₂ List.cons step.2.1 ih.2⟩

end
end IncrPP
end Incr
