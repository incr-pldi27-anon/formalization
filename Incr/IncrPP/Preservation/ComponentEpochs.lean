import Incr.IncrPP.Preservation.ComponentLists

/-!
# Pipeline epochs and original-position trace extension

Initialization epochs are actual recorded indices. Extending a trace does
not change an earlier step's component identity. These facts also exclude
any recorded history for a pending initialization at the next index.
-/

namespace Incr.IncrPP

variable {sig : Signature} {m : CommandModel sig} {h : Host sig}
  {executor : Executor} {prog : sig.Prog}

/-- Appending a step changes the current epoch exactly when that step initializes. -/
theorem latestPipeline_snoc (trace : Trace m h executor prog) (d : StepDerivation m h executor prog) :
    latestPipeline (trace ++ [d]) = match d.selection.init with
      | some init => some (trace.length, init)
      | none => latestPipeline trace := by
  cases init : d.selection.init <;> simp [latestPipeline, List.filterMap_append, init]

/-- A current epoch retains the initialization at its actual original index. -/
theorem latestPipeline_origin (trace : Trace m h executor prog) {entry : Nat} {init : PipelineInit sig}
    (latest : latestPipeline trace = some (entry, init)) :
    ∃ d, (trace)[entry]? = some d ∧ d.selection.init = some init := by
  have member := List.mem_of_getLast? latest
  obtain ⟨option, indexed, chosen⟩ := List.mem_filterMap.mp member
  obtain ⟨pos, bound, rfl⟩ := List.mem_mapIdx.mp indexed
  dsimp at chosen
  cases source : ((trace)[pos]).selection.init with
  | none => simp [source] at chosen
  | some found =>
    simp only [source, Option.map_some, Option.some.injEq, Prod.mk.injEq] at chosen
    obtain ⟨rfl, rfl⟩ := chosen
    exact ⟨(trace)[pos], List.getElem?_eq_getElem bound, source⟩

/-- Recorded epochs are strictly below the next recorded index. -/
theorem latestPipeline_entry_lt (trace : Trace m h executor prog) {entry : Nat} {init : PipelineInit sig}
    (latest : latestPipeline trace = some (entry, init)) : entry < trace.length := by
  obtain ⟨d, atPos, _⟩ := latestPipeline_origin trace latest
  exact (List.getElem?_eq_some_iff.mp atPos).choose

/-- Extension cannot change the component of any earlier recorded position. -/
theorem componentAt_append (trace extra : Trace m h executor prog) (pos : Nat)
    (d : StepDerivation m h executor prog) (bound : pos < trace.length) :
    componentAt (trace ++ extra) pos d = componentAt trace pos d := by
  cases head : d.selection.head <;>
    simp only [componentAt, head, List.take_append_of_le_length (Nat.succ_le_of_lt bound)]

/-- A pipeline step cannot belong to an initialization in its future. -/
theorem componentAt_pipeline_entry_le (trace : Trace m h executor prog) (pos : Nat)
    (d : StepDerivation m h executor prog) {entry slot : Nat}
    (component : componentAt trace pos d = some (.pipeline entry slot)) : entry ≤ pos := by
  cases head : d.selection.head with
  | standalone p => simp [componentAt, head] at component
  | pipeline p i =>
    simp only [componentAt, head] at component
    cases latest : latestPipeline (trace.take (pos + 1)) with
    | none => simp [latest] at component
    | some epoch =>
      rcases epoch with ⟨origin, init⟩
      simp only [latest, Option.map_some, Option.some.injEq, Component.pipeline.injEq] at component
      obtain ⟨rfl, rfl⟩ := component
      have bound := latestPipeline_entry_lt _ latest
      simp only [List.length_take] at bound
      exact Nat.le_of_lt_succ (Nat.lt_of_lt_of_le bound (Nat.min_le_left _ _))

/-- Closing positions retain their actual derivation and EOF input witness. -/
theorem mem_closingPositions_iff (trace : Trace m h executor prog) (k : Component) (position : Nat) :
    position ∈ closingPositions trace k ↔
      ∃ pos d, (trace)[pos]? = some d ∧ componentAt trace pos d = some k ∧
        (ProbeDerivation.input d.probe).flag = .eof ∧ position = paperPosition pos := by
  classical
  constructor
  · intro member
    rcases List.mem_filterMap.mp member with ⟨option, indexed, chosen⟩
    rcases List.mem_mapIdx.mp indexed with ⟨pos, bound, rfl⟩
    dsimp at chosen
    split at chosen
    next condition =>
      exact ⟨pos, (trace)[pos], List.getElem?_eq_getElem bound,
        condition.1, condition.2, (Option.some.inj chosen).symm⟩
    next => simp at chosen
  · rintro ⟨pos, d, atPos, component, eofFlag, rfl⟩
    rcases List.getElem?_eq_some_iff.mp atPos with ⟨bound, rfl⟩
    apply List.mem_filterMap.mpr
    refine ⟨_, List.mem_mapIdx.mpr ⟨pos, bound, rfl⟩, ?_⟩
    simp [component, eofFlag]

/-- The last step sees its own initialization before its probe is executed. -/
theorem componentAt_snoc (trace : Trace m h executor prog) (d : StepDerivation m h executor prog) :
    componentAt (trace ++ [d]) trace.length d = match d.selection.head with
      | .standalone _ => some (.standalone trace.length)
      | .pipeline _ slot => (latestPipeline (trace ++ [d])).map fun entry => .pipeline entry.1 slot := by
  unfold componentAt
  rw [show trace.length + 1 = (trace ++ [d]).length by simp, List.take_length]
  rfl

/-- Every pipeline component in the historical domain has a recorded initialization. -/
theorem componentDomain_pipeline_entry_lt (trace : Trace m h executor prog) {entry slot : Nat}
    (member : .pipeline entry slot ∈ componentDomain trace) : entry < trace.length := by
  obtain ⟨pos, d, atPos, kind⟩ := member
  rcases kind with ⟨p, _, equal⟩ | ⟨init, i, _, _, equal⟩
  · cases equal
  · cases equal
    exact (List.getElem?_eq_some_iff.mp atPos).choose

/-- A snoc extension preserves earlier component steps and adds only its own step. -/
theorem componentSteps_snoc (trace : Trace m h executor prog) (d : StepDerivation m h executor prog)
    (k : Component) :
    componentSteps (trace ++ [d]) k = componentSteps trace k ++
      if componentAt (trace ++ [d]) trace.length d = some k then [d] else [] := by
  classical
  have stable : trace.mapIdx (fun pos step => (componentAt (trace ++ [d]) pos step, step)) =
      trace.mapIdx (fun pos step => (componentAt trace pos step, step)) := by
    apply List.mapIdx_eq_mapIdx_iff.mpr
    intro pos bound
    rw [componentAt_append trace [d] pos _ bound]
  simp only [componentSteps, List.mapIdx_concat, List.filterMap_append]
  rw [stable]
  split <;> simp_all

/-- A closing list changes only for the component that actually consumes EOF. -/
theorem closingPositions_snoc (trace : Trace m h executor prog) (d : StepDerivation m h executor prog)
    (k : Component) :
    closingPositions (trace ++ [d]) k = closingPositions trace k ++
      if componentAt (trace ++ [d]) trace.length d = some k ∧
          (ProbeDerivation.input d.probe).flag = .eof then [paperPosition trace.length] else [] := by
  classical
  have stable :
      trace.mapIdx (fun pos step => if componentAt (trace ++ [d]) pos step = some k ∧
          (ProbeDerivation.input step.probe).flag = .eof then some (paperPosition pos) else none) =
      trace.mapIdx (fun pos step => if componentAt trace pos step = some k ∧
          (ProbeDerivation.input step.probe).flag = .eof then some (paperPosition pos) else none) := by
    apply List.mapIdx_eq_mapIdx_iff.mpr
    intro pos bound
    rw [componentAt_append trace [d] pos _ bound]
  simp only [closingPositions, List.mapIdx_concat, List.filterMap_append]
  rw [stable]
  split <;> simp_all

/-- A new component enters the historical domain only at its actual initialization or standalone step. -/
theorem componentDomain_snoc (trace : Trace m h executor prog) (d : StepDerivation m h executor prog)
    (k : Component) :
    k ∈ componentDomain (trace ++ [d]) ↔ k ∈ componentDomain trace ∨
      (∃ p, d.selection.head = .standalone p ∧ k = .standalone trace.length) ∨
      ∃ init slot, d.selection.init = some init ∧ slot < init.probes.length ∧
        k = .pipeline trace.length slot := by
  constructor
  · rintro ⟨pos, step, atPos, kind⟩
    by_cases old : pos < trace.length
    · left
      exact ⟨pos, step, by rwa [List.getElem?_append_left old] at atPos, kind⟩
    · have upper : pos ≤ trace.length := by
        have bound : pos < trace.length + 1 := by
          simpa only [List.length_append, List.length_singleton] using
            (List.getElem?_eq_some_iff.mp atPos).choose
        exact Nat.le_of_lt_succ bound
      have equal : pos = trace.length := Nat.le_antisymm upper (Nat.le_of_not_gt old)
      subst pos
      simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero,
        Option.some.injEq] at atPos
      subst step
      exact Or.inr kind
  · rintro (⟨pos, step, atPos, kind⟩ | kind)
    · have bound := (List.getElem?_eq_some_iff.mp atPos).choose
      exact ⟨pos, step, by rwa [List.getElem?_append_left bound], kind⟩
    · exact ⟨trace.length, d, by simp, kind⟩

/-- A pending initialization cannot already have a retained component step. -/
theorem componentSteps_fresh (trace : Trace m h executor prog) (entry slot : Nat)
    (fresh : trace.length ≤ entry) : componentSteps trace (.pipeline entry slot) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro d member
  obtain ⟨pos, atPos, component⟩ := (mem_componentSteps_iff trace _ d).mp member
  have before := componentAt_pipeline_entry_le trace pos d component
  have bound := (List.getElem?_eq_some_iff.mp atPos).choose
  exact Nat.not_lt_of_ge (Nat.le_trans fresh before) bound

/-- A pending initialization cannot already have a closing position. -/
theorem closingPositions_fresh (trace : Trace m h executor prog) (entry slot : Nat)
    (fresh : trace.length ≤ entry) : closingPositions trace (.pipeline entry slot) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro position member
  obtain ⟨pos, d, atPos, component, _, _⟩ := (mem_closingPositions_iff trace _ position).mp member
  have before := componentAt_pipeline_entry_le trace pos d component
  have bound := (List.getElem?_eq_some_iff.mp atPos).choose
  exact Nat.not_lt_of_ge (Nat.le_trans fresh before) bound

/-- A closing position is positive and lies within the recorded prefix. -/
theorem closingPositions_bounds (trace : Trace m h executor prog) (k : Component) (position : Nat)
    (member : position ∈ closingPositions trace k) : 0 < position ∧ position ≤ trace.length := by
  obtain ⟨pos, d, atPos, _, _, rfl⟩ := (mem_closingPositions_iff trace k position).mp member
  have bound := (List.getElem?_eq_some_iff.mp atPos).choose
  exact ⟨Nat.zero_lt_succ pos, Nat.succ_le_of_lt bound⟩

/-- A standalone identity is exactly its original recorded position. -/
theorem componentAt_standalone_index (trace : Trace m h executor prog) (pos : Nat)
    (d : StepDerivation m h executor prog) {entry : Nat}
    (component : componentAt trace pos d = some (.standalone entry)) : entry = pos := by
  cases head : d.selection.head with
  | standalone p =>
    simpa only [componentAt, head, Option.some.injEq, Component.standalone.injEq] using component.symm
  | pipeline p i =>
    cases latest : latestPipeline (trace.take (pos + 1)) <;>
      simp [componentAt, head, latest] at component

/-- No earlier standalone step has the next position as its identity. -/
theorem closingPositions_standalone_fresh (trace : Trace m h executor prog) (entry : Nat)
    (fresh : trace.length ≤ entry) : closingPositions trace (.standalone entry) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro position member
  obtain ⟨pos, d, atPos, component, _, _⟩ := (mem_closingPositions_iff trace _ position).mp member
  have equal := componentAt_standalone_index trace pos d component
  have bound := (List.getElem?_eq_some_iff.mp atPos).choose
  exact Nat.not_lt_of_ge (equal ▸ fresh) bound

end IncrPP
end Incr
