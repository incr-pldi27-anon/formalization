import Incr.Incr.Preservation.Statements

/-! # Component histories under trace extension -/

open Incr
namespace Incr.Incr

noncomputable section

variable {sig : Signature} {m : CommandModel sig} {h : Host sig}
  {executor : Executor} {prog : sig.Prog}

/-- A new initialization replaces the latest entry; other steps preserve it. -/
theorem latestPipeline_snoc (trace : Trace m h executor prog)
    (d : StepDerivation m h executor prog) :
    latestPipeline (trace ++ [d]) = selectedPipeline trace d.selection := by
  simp [latestPipeline, selectedPipeline, List.mapIdx_append, List.filterMap_append,
    List.getLast?_append]
  cases d.selection.init <;> simp

/-- Appending steps does not change earlier component identities. -/
theorem componentAt_append_left (xs ys : Trace m h executor prog)
    (pos : Nat) (d : StepDerivation m h executor prog) (hp : pos < xs.length) :
    componentAt (xs ++ ys) pos d = componentAt xs pos d := by
  unfold componentAt
  rw [List.take_append_of_le_length (by omega)]

/-- The last step uses the component identity at its selection boundary. -/
theorem componentAt_snoc_last (trace : Trace m h executor prog)
    (d : StepDerivation m h executor prog) :
    componentAt (trace ++ [d]) trace.length d =
      match d.selection.head with
      | .standalone _ => some (.standalone trace.length)
      | .pipeline _ i => selectedComponent trace d.selection i := by
  have ht : (trace ++ [d]).take (trace.length + 1) = trace ++ [d] := by
    apply List.take_of_length_le
    simp
  simp only [componentAt, ht, latestPipeline_snoc, selectedComponent]
  rfl

/-- Component projection adds exactly the matching final step. -/
theorem componentSteps_snoc (trace : Trace m h executor prog)
    (d : StepDerivation m h executor prog) (k : Component) :
    componentSteps (trace ++ [d]) k = componentSteps trace k ++
      (if componentAt (trace ++ [d]) trace.length d = some k then [d] else []) := by
  classical
  unfold componentSteps
  rw [List.mapIdx_append, List.filterMap_append]
  congr 1
  · congr 1
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      have hit : i < trace.length := by simpa using hi
      simp only [List.getElem_mapIdx]
      rw [componentAt_append_left trace [d] i ((trace)[i]) hit]
  · split <;> simp_all

/-- Open history adds a step exactly when its component and input flag match. -/
theorem openHistory_snoc (trace : Trace m h executor prog)
    (d : StepDerivation m h executor prog) (k : Component) :
    openHistory (trace ++ [d]) k = openHistory trace k ++
      (if componentAt (trace ++ [d]) trace.length d = some k ∧
        (ProbeDerivation.input d.probe).flag = .open then [d] else []) := by
  classical
  simp only [openHistory, componentSteps_snoc, List.filter_append]
  by_cases hk : componentAt (trace ++ [d]) trace.length d = some k
  · simp only [hk, ite_true, true_and]
    by_cases ho : (ProbeDerivation.input d.probe).flag = .open <;> simp [ho]
  · simp [hk]

/-- A closure witness is either earlier or the new EOF-input step. -/
theorem slotClosed_snoc (trace : Trace m h executor prog)
    (d : StepDerivation m h executor prog) (entry slot : Nat) :
    slotClosed (trace ++ [d]) entry slot ↔ slotClosed trace entry slot ∨
      (componentAt (trace ++ [d]) trace.length d = some (.pipeline entry slot) ∧
        (ProbeDerivation.input d.probe).flag = .eof) := by
  classical
  simp only [slotClosed, componentSteps_snoc, List.mem_append]
  by_cases hk : componentAt (trace ++ [d]) trace.length d = some (.pipeline entry slot)
  · simp [hk]
  · simp [hk]

/-- Projection membership retains its actual whole-trace position. -/
theorem mem_componentSteps_iff (trace : Trace m h executor prog)
    (k : Component) (d : StepDerivation m h executor prog) :
    d ∈ componentSteps trace k ↔ ∃ pos, (trace)[pos]? = some d ∧
      componentAt trace pos d = some k := by
  classical
  simp only [componentSteps, List.mem_filterMap]
  constructor
  · rintro ⟨pair, hp, he⟩
    obtain ⟨pos, hpos, rfl⟩ := List.mem_mapIdx.mp hp
    split at he
    · cases Option.some.inj he
      exact ⟨pos, by simp, by assumption⟩
    · contradiction
  · rintro ⟨pos, hp, hk⟩
    obtain ⟨hpos, hd⟩ := List.getElem?_eq_some_iff.mp hp
    refine ⟨(some k, d), ?_, by simp⟩
    apply List.mem_mapIdx.mpr
    exact ⟨pos, hpos, by simp [hd, hk]⟩

/-- A closed slot has an EOF witness at a recorded position. -/
theorem slotClosed_iff_position (trace : Trace m h executor prog) (entry slot : Nat) :
    slotClosed trace entry slot ↔ ∃ pos d, (trace)[pos]? = some d ∧
      componentAt trace pos d = some (.pipeline entry slot) ∧
      (ProbeDerivation.input d.probe).flag = .eof := by
  simp only [slotClosed, mem_componentSteps_iff]
  constructor
  · rintro ⟨d, ⟨pos, hp, hk⟩, hf⟩
    exact ⟨pos, d, hp, hk, hf⟩
  · rintro ⟨pos, d, hp, hk, hf⟩
    exact ⟨d, ⟨pos, hp, hk⟩, hf⟩

/-- Existing closure order extends when all lower slots already closed. -/
theorem ClosingOrder.snoc {trace : Trace m h executor prog}
    (order : ClosingOrder trace) (d : StepDerivation m h executor prog)
    (closed : ∀ entry j,
      componentAt (trace ++ [d]) trace.length d = some (.pipeline entry j) →
      (ProbeDerivation.input d.probe).flag = .eof →
      ∀ i, i < j → slotClosed trace entry i) : ClosingOrder (trace ++ [d]) := by
  intro pos e entry j hp hk hf i hij
  have hpos : pos < trace.length + 1 := by
    have := (List.getElem?_eq_some_iff.mp hp).1
    simpa using this
  by_cases hlt : pos < trace.length
  · have he : (trace)[pos]? = some e := by
      simpa [List.getElem?_append, hlt] using hp
    have hk' : componentAt trace pos e = some (.pipeline entry j) := by
      simpa [componentAt_append_left trace [d] pos e hlt] using hk
    obtain ⟨earlier, previous, hl, hearlier, hc, hflag⟩ := order pos e entry j he hk' hf i hij
    refine ⟨earlier, previous, hl, ?_, ?_, hflag⟩
    · simpa [List.getElem?_append, show earlier < trace.length by omega] using hearlier
    · simpa [componentAt_append_left trace [d] earlier previous (by omega)] using hc
  · have hp' : pos = trace.length := by omega
    subst pos
    have hed : e = d := by simpa using hp.symm
    subst e
    obtain ⟨earlier, previous, hearlier, hc, hflag⟩ :=
      (slotClosed_iff_position trace entry i).mp (closed entry j hk hf i hij)
    have hl : earlier < trace.length := (List.getElem?_eq_some_iff.mp hearlier).1
    refine ⟨earlier, previous, hl, ?_, ?_, hflag⟩
    · simpa [List.getElem?_append, hl] using hearlier
    · simpa [componentAt_append_left trace [d] earlier previous hl] using hc

/-- The latest entry points to an actual initialization step. -/
theorem latestPipeline_witness (trace : Trace m h executor prog)
    {entry : Nat} {init : PipelineInit sig}
    (latest : latestPipeline trace = some (entry, init)) :
    ∃ d, (trace)[entry]? = some d ∧ d.selection.init = some init := by
  induction trace using List.reverseRecOn with
  | nil => simp [latestPipeline] at latest
  | append_singleton trace d ih =>
      rw [latestPipeline_snoc] at latest
      cases hi : d.selection.init with
      | none =>
          simp only [selectedPipeline, hi] at latest
          obtain ⟨e, he, hei⟩ := ih latest
          have hl := (List.getElem?_eq_some_iff.mp he).1
          exact ⟨e, by simpa [List.getElem?_append, hl] using he, hei⟩
      | some init' =>
          simp only [selectedPipeline, hi, Option.some.injEq, Prod.mk.injEq] at latest
          obtain ⟨rfl, rfl⟩ := latest
          exact ⟨d, by simp, hi⟩

/-- Every entry index is strictly below the trace length. -/
theorem latestPipeline_entry_lt {trace : Trace m h executor prog}
    {entry : Nat} {init : PipelineInit sig}
    (latest : latestPipeline trace = some (entry, init)) : entry < trace.length := by
  obtain ⟨d, hd, _⟩ := latestPipeline_witness trace latest
  exact (List.getElem?_eq_some_iff.mp hd).1

/-- A pipeline component cannot precede its initialization position. -/
theorem componentAt_pipeline_entry_le {trace : Trace m h executor prog}
    {pos entry slot : Nat} {d : StepDerivation m h executor prog}
    (hc : componentAt trace pos d = some (.pipeline entry slot)) : entry ≤ pos := by
  unfold componentAt at hc
  cases hh : d.selection.head with
  | standalone p => simp [hh] at hc
  | pipeline p i =>
      simp only [hh] at hc
      cases hl : latestPipeline (trace.take (pos + 1)) with
      | none => simp [hl] at hc
      | some pair =>
          obtain ⟨e, init⟩ := pair
          simp only [hl, Option.map_some, Option.some.injEq, Component.pipeline.injEq] at hc
          obtain ⟨rfl, rfl⟩ := hc
          have hb := latestPipeline_entry_lt hl
          have ht : (trace.take (pos + 1)).length ≤ pos + 1 := List.length_take_le _ _
          omega

/-- A new invocation has no steps from a preceding invocation. -/
theorem componentSteps_future_entry (trace : Trace m h executor prog)
    {entry : Nat} (slot : Nat) (future : trace.length ≤ entry) :
    componentSteps trace (.pipeline entry slot) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro d hd
  obtain ⟨pos, hp, hc⟩ := (mem_componentSteps_iff trace _ d).mp hd
  have hl := (List.getElem?_eq_some_iff.mp hp).1
  have he := componentAt_pipeline_entry_le hc
  omega

end

end Incr.Incr
