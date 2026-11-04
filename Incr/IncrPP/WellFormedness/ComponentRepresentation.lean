import Incr.IncrPP.WellFormedness.Host
import Incr.IncrPP.WellFormedness.ExitOrder
import Incr.IncrPP.Preservation.Allocation

/-!
# Component-domain and position representation obligations

These proofs connect original recorded indices, initialized histories, and
actual allocated slots. Retirement excludes unclosed older components.
Closing uniqueness justifies the first-close implementation of `lastPosition`.
-/

namespace Incr.IncrPP

variable {sig : Signature} {m : CommandModel sig} {h : Host sig}
  {executor : Executor} {prog : sig.Prog}

/-- Component step lists retain original global positions, not filtered positions. -/
theorem componentPositions_iff (trace : Trace m h executor prog) (k : Component) (position : Nat) :
    position ∈ componentPositions trace k ↔
      ∃ pos d, (trace)[pos]? = some d ∧ componentAt trace pos d = some k ∧
        position = paperPosition pos := by
  classical
  constructor
  · intro member
    rcases List.mem_filterMap.mp member with ⟨option, indexed, chosen⟩
    rcases List.mem_mapIdx.mp indexed with ⟨pos, bound, rfl⟩
    dsimp at chosen
    split at chosen
    next component =>
      exact ⟨pos, (trace)[pos], List.getElem?_eq_getElem bound, component,
        (Option.some.inj chosen).symm⟩
    next => simp at chosen
  · rintro ⟨pos, d, atPos, component, rfl⟩
    rcases List.getElem?_eq_some_iff.mp atPos with ⟨bound, rfl⟩
    apply List.mem_filterMap.mpr
    refine ⟨_, List.mem_mapIdx.mpr ⟨pos, bound, rfl⟩, ?_⟩
    simp [component]

/-- A host-disciplined invocation has at most one actual closing transition. -/
theorem component_closes_once (host : HostWellFormed m h)
    {start : World sig} (pre : Prefix m h executor prog start) (operational : Operational pre)
    (k : Component) (present : k ∈ componentDomain pre.trace) :
    (closingPositions pre.trace k).length ≤ 1 := by
  obtain ⟨position, step, atPos, kind⟩ := present
  exact Operational.closing_unique host pre operational k

/-- History-based liveness agrees with the actual current pipeline's allocated slots. -/
theorem livePipelineComponent_iff (host : HostWellFormed m h)
    {start : World sig} (pre : Prefix m h executor prog start) (operational : Operational pre)
    (entry slot : Nat) :
    LivePipelineComponent pre.trace entry slot ↔
      (∃ init, latestPipeline pre.trace = some (entry, init)) ∧
        slot ∈ FMap.dom pre.final.sandbox ∧ slot ∈ FMap.dom pre.final.buffer := by
  classical
  have allocation := Operational.slotAllocation_final host pre operational
  have buffersEq : FMap.dom pre.final.buffer =
      (Boundary.final : Boundary pre).unclosedSlots := allocation.buffers
  have sandboxesEq : FMap.dom pre.final.sandbox =
      (Boundary.final : Boundary pre).unclosedSlots := allocation.sandboxes
  constructor
  · rintro ⟨domain, unclosed⟩
    have present : .pipeline entry slot ∈ (Boundary.final : Boundary pre).componentDomain := by
      simpa [Boundary.componentDomain, Boundary.selection?] using domain
    have current : (Boundary.final : Boundary pre).currentEntry = some entry := by
      by_contra retired
      exact allocation.retired entry slot present retired unclosed
    have epoch : (latestPipeline pre.trace).map Prod.fst = some entry := current
    obtain ⟨pair, latest, index⟩ := Option.map_eq_some_iff.mp epoch
    rcases pair with ⟨origin, init⟩
    dsimp at index
    subst entry
    refine ⟨⟨init, latest⟩, ?_, ?_⟩
    · rw [sandboxesEq]
      exact ⟨origin, current, present, unclosed⟩
    · rw [buffersEq]
      exact ⟨origin, current, present, unclosed⟩
  · rintro ⟨⟨init, latest⟩, _, buffer⟩
    rw [buffersEq] at buffer
    obtain ⟨origin, current, domain, unclosed⟩ := buffer
    have epoch : (latestPipeline pre.trace).map Prod.fst = some origin := current
    rw [latest] at epoch
    have equal : entry = origin := Option.some.inj epoch
    subst origin
    refine ⟨?_, unclosed⟩
    simpa [Boundary.componentDomain, Boundary.selection?] using domain

end IncrPP
end Incr
