import Incr.IncrPP.Semantics.Components

/-!
# Original indices in filtered component histories

These list facts retain the original trace index after filtering. They need
no host discipline, timestamp assumptions, or terminating execution.
-/

namespace Incr.IncrPP

variable {sig : Signature} {m : CommandModel sig} {h : Host sig}
  {executor : Executor} {prog : sig.Prog}

/-- A retained component step comes from its actual position in the whole trace. -/
theorem mem_componentSteps_iff (trace : Trace m h executor prog) (k : Component)
    (d : StepDerivation m h executor prog) :
    d ∈ componentSteps trace k ↔
      ∃ pos, (trace)[pos]? = some d ∧ componentAt trace pos d = some k := by
  classical
  constructor
  · intro member
    rcases List.mem_filterMap.mp member with ⟨pair, indexed, chosen⟩
    rcases List.mem_mapIdx.mp indexed with ⟨pos, bound, rfl⟩
    dsimp at chosen
    split at chosen
    next component =>
      have equal := Option.some.inj chosen
      subst d
      exact ⟨pos, List.getElem?_eq_getElem bound, component⟩
    next => simp at chosen
  · rintro ⟨pos, atPos, component⟩
    rcases List.getElem?_eq_some_iff.mp atPos with ⟨bound, rfl⟩
    apply List.mem_filterMap.mpr
    refine ⟨_, List.mem_mapIdx.mpr ⟨pos, bound, rfl⟩, ?_⟩
    simp [component]

/-- Access positions retain both the component identity and the accessed path. -/
theorem mem_accessPositions_iff (trace : Trace m h executor prog) (k : Component)
    (q : sig.Path) (position : Nat) :
    position ∈ accessPositions trace k q ↔
      ∃ pos d, (trace)[pos]? = some d ∧ componentAt trace pos d = some k ∧
        q ∈ d.accesses ∧ position = paperPosition pos := by
  classical
  constructor
  · intro member
    rcases List.mem_filterMap.mp member with ⟨option, indexed, chosen⟩
    rcases List.mem_mapIdx.mp indexed with ⟨pos, bound, rfl⟩
    dsimp at chosen
    split at chosen
    next condition =>
      have equal := Option.some.inj chosen
      exact ⟨pos, (trace)[pos], List.getElem?_eq_getElem bound,
        condition.1, condition.2, equal.symm⟩
    next => simp at chosen
  · rintro ⟨pos, d, atPos, component, path, rfl⟩
    rcases List.getElem?_eq_some_iff.mp atPos with ⟨bound, rfl⟩
    apply List.mem_filterMap.mpr
    refine ⟨_, List.mem_mapIdx.mpr ⟨pos, bound, rfl⟩, ?_⟩
    simp [component, path]

end IncrPP
end Incr
