import Incr.IncrPP.Preservation.FilesystemEffects

/-!
# Retained positions in trace extensions

These lemmas transport actual indexed component facts, not arbitrary
assumptions about an endpoint or a future continuation.
-/

namespace Incr.IncrPP

noncomputable section

variable {sig : Signature} {m : CommandModel sig} {h : Host sig}
  {executor : Executor} {prog : sig.Prog}

/-- A recorded component identity remains in the domain after extension. -/
theorem componentDomain_append_subset (trace extra : Trace m h executor prog) :
    componentDomain trace ⊆ componentDomain (trace ++ extra) := by
  rintro k ⟨pos, d, atPos, kind⟩
  have bound := (List.getElem?_eq_some_iff.mp atPos).choose
  exact ⟨pos, d, by rwa [List.getElem?_append_left bound], kind⟩

/-- A retained position is the same component step in every extension. -/
theorem componentSteps_append_subset (trace extra : Trace m h executor prog) (k : Component) :
    ∀ d ∈ componentSteps trace k, d ∈ componentSteps (trace ++ extra) k := by
  intro d member
  obtain ⟨pos, atPos, component⟩ := (mem_componentSteps_iff trace k d).mp member
  have bound := (List.getElem?_eq_some_iff.mp atPos).choose
  apply (mem_componentSteps_iff (trace ++ extra) k d).mpr
  exact ⟨pos, by rwa [List.getElem?_append_left bound], by
    rwa [componentAt_append trace extra pos d bound]⟩

/-- Every retained write remains a write of the same component. -/
theorem componentWrites_append_subset (trace extra : Trace m h executor prog) (k : Component) :
    componentWrites trace k ⊆ componentWrites (trace ++ extra) k := by
  rintro q ⟨d, member, path⟩
  exact ⟨d, componentSteps_append_subset trace extra k d member, path⟩

/-- Every retained access remains an access of the same component. -/
theorem componentAccesses_append_subset (trace extra : Trace m h executor prog) (k : Component) :
    componentAccesses trace k ⊆ componentAccesses (trace ++ extra) k := by
  rintro q (⟨d, member, path⟩ | ⟨d, member, path⟩)
  · exact Or.inl ⟨d, componentSteps_append_subset trace extra k d member, path⟩
  · exact Or.inr ⟨d, componentSteps_append_subset trace extra k d member, path⟩

/-- Existing access positions survive extension with their original one-based indices. -/
theorem accessPositions_append_member (trace extra : Trace m h executor prog) (k : Component)
    (q : sig.Path) (position : Nat) (member : position ∈ accessPositions trace k q) :
    position ∈ accessPositions (trace ++ extra) k q := by
  obtain ⟨pos, d, atPos, component, path, equal⟩ := (mem_accessPositions_iff trace k q position).mp member
  have bound := (List.getElem?_eq_some_iff.mp atPos).choose
  apply (mem_accessPositions_iff (trace ++ extra) k q position).mpr
  exact ⟨pos, d, by rwa [List.getElem?_append_left bound], by
    rwa [componentAt_append trace extra pos d bound], path, equal⟩

/-- Existing closing positions survive extension with their original one-based indices. -/
theorem closingPositions_append_member (trace extra : Trace m h executor prog) (k : Component)
    (position : Nat) (member : position ∈ closingPositions trace k) :
    position ∈ closingPositions (trace ++ extra) k := by
  obtain ⟨pos, d, atPos, component, flag, equal⟩ := (mem_closingPositions_iff trace k position).mp member
  have bound := (List.getElem?_eq_some_iff.mp atPos).choose
  apply (mem_closingPositions_iff (trace ++ extra) k position).mpr
  exact ⟨pos, d, by rwa [List.getElem?_append_left bound], by
    rwa [componentAt_append trace extra pos d bound], flag, equal⟩

/-- Every extension access no later than the old trace belongs to the old trace. -/
theorem accessPositions_append_old (trace extra : Trace m h executor prog) (k : Component)
    (q : sig.Path) (position : Nat) (member : position ∈ accessPositions (trace ++ extra) k q)
    (bound : position ≤ trace.length) : position ∈ accessPositions trace k q := by
  obtain ⟨pos, d, atPos, component, path, equal⟩ :=
    (mem_accessPositions_iff (trace ++ extra) k q position).mp member
  have old : pos < trace.length := by
    rw [equal] at bound
    exact Nat.lt_of_succ_le bound
  apply (mem_accessPositions_iff trace k q position).mpr
  exact ⟨pos, d, by rwa [List.getElem?_append_left old] at atPos,
    by rwa [componentAt_append trace extra pos d old] at component, path, equal⟩

/-- Once a path was accessed, its first access cannot change under extension. -/
theorem firstAccess_append (trace extra : Trace m h executor prog) (k : Component) (q : sig.Path)
    (accessed : q ∈ componentAccesses trace k) :
    firstAccess (trace ++ extra) k q (componentAccesses_append_subset trace extra k accessed) =
      firstAccess trace k q accessed := by
  let longer := componentAccesses_append_subset trace extra k accessed
  have oldSpec := firstAccess_spec trace k q accessed
  have longSpec := firstAccess_spec (trace ++ extra) k q longer
  have longLe : firstAccess (trace ++ extra) k q longer ≤ firstAccess trace k q accessed :=
    longSpec.2.2.2 _ (accessPositions_append_member trace extra k q _ oldSpec.1)
  have longOld := accessPositions_append_old trace extra k q _ longSpec.1
    (Nat.le_trans longLe oldSpec.2.2.1)
  exact Nat.le_antisymm longLe (oldSpec.2.2.2 _ longOld)

/-- The chronological closing list is itself a prefix after trace extension. -/
theorem closingPositions_append_prefix (trace extra : Trace m h executor prog) (k : Component) :
    (closingPositions trace k).IsPrefix (closingPositions (trace ++ extra) k) := by
  classical
  have stable :
      trace.mapIdx (fun pos step => if componentAt (trace ++ extra) pos step = some k ∧
          (ProbeDerivation.input step.probe).flag = .eof then some (paperPosition pos) else none) =
      trace.mapIdx (fun pos step => if componentAt trace pos step = some k ∧
          (ProbeDerivation.input step.probe).flag = .eof then some (paperPosition pos) else none) := by
    apply List.mapIdx_eq_mapIdx_iff.mpr
    intro pos bound
    rw [componentAt_append trace extra pos _ bound]
  unfold closingPositions
  rw [List.mapIdx_append, List.filterMap_append, stable]
  exact ⟨_, rfl⟩

/-- An extension closing at an old position was already present in the old trace. -/
theorem closingPositions_append_old (trace extra : Trace m h executor prog) (k : Component)
    (position : Nat) (member : position ∈ closingPositions (trace ++ extra) k)
    (bound : position ≤ trace.length) : position ∈ closingPositions trace k := by
  obtain ⟨pos, d, atPos, component, flag, equal⟩ :=
    (mem_closingPositions_iff (trace ++ extra) k position).mp member
  have old : pos < trace.length := by
    rw [equal] at bound
    exact Nat.lt_of_succ_le bound
  apply (mem_closingPositions_iff trace k position).mpr
  exact ⟨pos, d, by rwa [List.getElem?_append_left old] at atPos,
    by rwa [componentAt_append trace extra pos d old] at component, flag, equal⟩

/-- The paper's open endpoint or actual first close never moves backwards under extension. -/
theorem lastPosition_append_le (trace extra : Trace m h executor prog) (k : Component) :
    lastPosition trace k ≤ lastPosition (trace ++ extra) k := by
  obtain ⟨suffix, joined⟩ := closingPositions_append_prefix trace extra k
  cases old : closingPositions trace k with
  | nil =>
    cases new : closingPositions (trace ++ extra) k with
    | nil => simp [lastPosition, old, new]
    | cons position rest =>
      have present : position ∈ closingPositions (trace ++ extra) k := by simp [new]
      have notOld : trace.length < position := by
        by_contra notGreater
        have member := closingPositions_append_old trace extra k position present (Nat.le_of_not_gt notGreater)
        simp [old] at member
      simpa [lastPosition, old, new] using Nat.le_of_lt notOld
  | cons position rest =>
    rw [old] at joined
    have new : closingPositions (trace ++ extra) k = position :: (rest ++ suffix) := by
      simpa using joined.symm
    simp [lastPosition, old, new]

/-- Exit ordering restricts to every recorded prefix without extra hypotheses. -/
theorem ExitOrdered.of_append (trace extra : Trace m h executor prog)
    (ordered : ExitOrdered (trace ++ extra)) : ExitOrdered trace := by
  intro entry i j memI memJ different q shared
  have longI := componentDomain_append_subset trace extra memI
  have longJ := componentDomain_append_subset trace extra memJ
  have longShared : q ∈ componentWrites (trace ++ extra) (.pipeline entry i) ∩
      componentAccesses (trace ++ extra) (.pipeline entry j) :=
    ⟨componentWrites_append_subset trace extra _ shared.1,
      componentAccesses_append_subset trace extra _ shared.2⟩
  have ordering := ordered entry i j longI longJ different q longShared
  rw [firstAccess_append trace extra _ q shared.2,
      firstAccess_append trace extra _ q (Or.inr shared.1)] at ordering
  rcases ordering with left | right
  · exact Or.inl (Nat.lt_of_le_of_lt (lastPosition_append_le trace extra _) left)
  · exact Or.inr (Nat.lt_of_le_of_lt (lastPosition_append_le trace extra _) right)

/-- The printed prefix-closure field for any actual shorter prefix. -/
theorem ExitOrdered.of_trace_isPrefix {start : World sig}
    {long short : Prefix m h executor prog start}
    (ordered : ExitOrdered long.trace) (shorter : short.trace.IsPrefix long.trace) :
    ExitOrdered short.trace := by
  obtain ⟨extra, joined⟩ := shorter
  rw [← joined] at ordered
  exact ExitOrdered.of_append short.trace extra ordered

end
end IncrPP
end Incr
