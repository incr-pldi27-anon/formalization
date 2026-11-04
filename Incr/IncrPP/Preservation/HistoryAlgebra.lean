import Incr.IncrPP.Preservation.Snapshots

/-!
# Chronological history algebra for E.4

These mathematical folds use the retained input and complete result maps.
They do not add an execution domain or assume a future command call.
-/

namespace Incr.IncrPP

noncomputable section

variable {sig : Signature} {m : CommandModel sig} {h : Host sig}
  {executor : Executor} {prog : sig.Prog}

/-- An unclosed component contains only open-input judgments. -/
theorem componentSteps_all_open (trace : Trace m h executor prog) (k : Component)
    (unclosed : closingPositions trace k = []) :
    ∀ d ∈ componentSteps trace k, (ProbeDerivation.input d.probe).flag = .open := by
  intro d member
  cases flag : (ProbeDerivation.input d.probe).flag with
  | «open» => rfl
  | eof =>
    obtain ⟨pos, atPos, component⟩ := (mem_componentSteps_iff trace k d).mp member
    have closed : paperPosition pos ∈ closingPositions trace k :=
      (mem_closingPositions_iff trace k _).mpr ⟨pos, d, atPos, component, flag, rfl⟩
    rw [unclosed] at closed
    contradiction

/-- Filtering an unclosed component to open judgments discards nothing. -/
theorem openSteps_eq_componentSteps (trace : Trace m h executor prog) (k : Component)
    (unclosed : closingPositions trace k = []) : openSteps trace k = componentSteps trace k := by
  apply List.filter_eq_self.mpr
  intro d member
  simp [componentSteps_all_open trace k unclosed d member]

/-- The chronological patch fold appends the new result patch on the right. -/
theorem historyPatch_snoc (steps : Trace m h executor prog) (d : StepDerivation m h executor prog) :
    historyPatch (steps ++ [d]) = historyPatch steps ⊎ (ProbeDerivation.result d.probe).patch := by
  simp [historyPatch, List.foldl_append]

/-- Historical writes retain every patch key, including deletion keys. -/
theorem historyWrites_snoc (steps : Trace m h executor prog) (d : StepDerivation m h executor prog) :
    historyWrites (steps ++ [d]) = historyWrites steps ∪ FMap.dom (ProbeDerivation.result d.probe).patch := by
  ext q
  simp [historyWrites, or_and_right, exists_or]

/-- A patch fold never loses keys from the initial patch or a later patch. -/
theorem historyPatch_fold_domain (steps : Trace m h executor prog) (initial : Patch sig) :
    FMap.dom (steps.foldl (fun patch d => patch ⊎ (ProbeDerivation.result d.probe).patch) initial) =
      FMap.dom initial ∪ historyWrites steps := by
  induction steps generalizing initial with
  | nil => simp [historyWrites]
  | cons d rest ih =>
    rw [List.foldl_cons, ih, FMap.dom_merge_union]
    ext q
    simp [historyWrites, or_and_right, exists_or, or_assoc]

/-- The accumulated patch domain is exactly the union of all actual write keys. -/
theorem historyPatch_domain (steps : Trace m h executor prog) :
    FMap.dom (historyPatch steps) = historyWrites steps := by
  simpa [historyPatch] using historyPatch_fold_domain steps (∅ : Patch sig)

/-- Restricted reads use the writes strictly before the new judgment. -/
theorem historyReads_snoc (steps : Trace m h executor prog) (d : StepDerivation m h executor prog) :
    historyReads (steps ++ [d]) = historyReads steps ⊎
      ((ProbeDerivation.result d.probe).reads ↾ (historyWrites steps)ᶜ) := by
  have stable :
      steps.mapIdx (fun j old => (ProbeDerivation.result old.probe).reads ↾
        (historyWrites ((steps ++ [d]).take j))ᶜ) =
      steps.mapIdx (fun j old => (ProbeDerivation.result old.probe).reads ↾
        (historyWrites (steps.take j))ᶜ) := by
    apply List.mapIdx_eq_mapIdx_iff.mpr
    intro j bound
    rw [List.take_append_of_le_length (Nat.le_of_lt bound)]
  unfold historyReads
  rw [List.mapIdx_concat, stable, List.foldl_append]
  simp

/-- Restricted write dependencies have the same chronological snoc equation. -/
theorem historyWriteDeps_snoc (steps : Trace m h executor prog) (d : StepDerivation m h executor prog) :
    historyWriteDeps (steps ++ [d]) = historyWriteDeps steps ⊎
      ((ProbeDerivation.result d.probe).writes ↾ (historyWrites steps)ᶜ) := by
  have stable :
      steps.mapIdx (fun j old => (ProbeDerivation.result old.probe).writes ↾
        (historyWrites ((steps ++ [d]).take j))ᶜ) =
      steps.mapIdx (fun j old => (ProbeDerivation.result old.probe).writes ↾
        (historyWrites (steps.take j))ᶜ) := by
    apply List.mapIdx_eq_mapIdx_iff.mpr
    intro j bound
    rw [List.take_append_of_le_length (Nat.le_of_lt bound)]
  unfold historyWriteDeps
  rw [List.mapIdx_concat, stable, List.foldl_append]
  simp

/-- Partial concatenation extends only an open accumulated chunk. -/
theorem concatenate_snoc (chunks : List Chunk) (previous next : Chunk)
    (prior : concatenate chunks = some previous) (openFlag : previous.flag = .open) :
    concatenate (chunks ++ [next]) = some (Chunk.concat previous next openFlag) := by
  unfold concatenate at prior ⊢
  rw [List.foldlM_append]
  simp [prior, openFlag]

/-- Restriction keeps exactly the map keys inside the stated path set. -/
theorem restriction_domain {K V : Type} (map : FMap K V) (paths : Set K) :
    FMap.dom (map ↾ paths) = FMap.dom map ∩ paths := by
  classical
  ext q
  change q ∈ (map ↾ paths) ↔ q ∈ map ∧ q ∈ paths
  rw [Finmap.mem_iff]
  constructor
  · rintro ⟨value, lookup⟩
    have kept := (FMap.get_restrict_eq_some map paths q value).mp lookup
    exact ⟨Finmap.mem_of_lookup_eq_some kept.2, kept.1⟩
  · rintro ⟨member, path⟩
    obtain ⟨value, lookup⟩ := Finmap.mem_iff.mp member
    exact ⟨value, (FMap.get_restrict_eq_some map paths q value).mpr ⟨path, lookup⟩⟩

/-- The shared accumulator's concrete filter is the printed complement restriction. -/
theorem filter_unwritten_eq_restrict {K V W : Type} [DecidableEq K]
    (map : FMap K V) (patch : FMap K W) :
    FMap.filterKeys (fun q => q ∉ FMap.keys patch) map = map ↾ (FMap.dom patch)ᶜ := by
  classical
  apply Finmap.ext_lookup
  intro q
  change FMap.get (FMap.filterKeys (fun q => q ∉ FMap.keys patch) map) q =
    FMap.get (map ↾ (FMap.dom patch)ᶜ) q
  rw [FMap.get_filterKeys, FMap.get_restrict]
  by_cases written : q ∈ FMap.dom patch
  · have key : q ∈ FMap.keys patch := written
    simp [written, key]
  · have key : q ∉ FMap.keys patch := written
    simp [written, key]

/-- Dropped dependencies already occur in an earlier patch, so the full access envelope is unchanged. -/
theorem history_dependency_envelope (steps : Trace m h executor prog) :
    historyWrites steps ∪ {q | ∃ d ∈ steps,
      q ∈ FMap.dom (ProbeDerivation.result d.probe).reads ∪ FMap.dom (ProbeDerivation.result d.probe).writes} =
      historyWrites steps ∪ FMap.dom (historyReads steps) ∪ FMap.dom (historyWriteDeps steps) := by
  classical
  induction steps using List.reverseRecOn with
  | nil => simp [historyWrites, historyReads, historyWriteDeps]
  | append_singleton xs d ih =>
    simp only [historyWrites_snoc, historyReads_snoc, historyWriteDeps_snoc,
      FMap.dom_merge_union, restriction_domain]
    ext q
    have previous := Set.ext_iff.mp ih q
    simp only [Set.mem_union, Set.mem_ofPred_eq] at previous
    by_cases written : q ∈ historyWrites xs
    · simp [written]
    · simp only [written, false_or] at previous
      simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_ofPred_eq,
        List.mem_append, List.mem_singleton, or_and_right, exists_or, exists_eq_left,
        written, false_or, not_false_eq_true, and_true]
      simp only [previous, or_assoc, or_left_comm, or_comm]

/-- The five accumulation equations over an arbitrary chronological retained history. -/
structure HistoryFields (steps : Trace m h executor prog) (sb : Sandbox sig) : Prop where
  patch : sb.patch = historyPatch steps
  input : concatenate (steps.map (fun d => ProbeDerivation.input d.probe)) = some sb.input
  output : concatenate (steps.map (fun d => (ProbeDerivation.result d.probe).output)) = some sb.output
  reads : sb.reads = historyReads steps
  writes : sb.writes = historyWriteDeps steps

/-- Empty retained history has precisely the printed initial accumulated fields. -/
theorem HistoryFields.initial (fs : FS sig) :
    HistoryFields ([] : Trace m h executor prog) (Sandbox.initial fs) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The shared accumulator implements the chronological history equations exactly. -/
theorem HistoryFields.accumulate (steps : Trace m h executor prog) (d : StepDerivation m h executor prog)
    (sb : Sandbox sig) (fields : HistoryFields steps sb)
    (hin : sb.input.flag = .open) (hout : sb.output.flag = .open) :
    HistoryFields (steps ++ [d])
      (sb.accumulate (ProbeDerivation.input d.probe) (ProbeDerivation.result d.probe) hin hout) := by
  constructor
  · change sb.patch ⊎ (ProbeDerivation.result d.probe).patch = _
    rw [historyPatch_snoc, fields.patch]
  · change concatenate ((steps ++ [d]).map (fun d => ProbeDerivation.input d.probe)) =
      some (Chunk.concat sb.input (ProbeDerivation.input d.probe) hin)
    rw [List.map_append, List.map_singleton]
    exact concatenate_snoc _ _ _ fields.input hin
  · change concatenate ((steps ++ [d]).map (fun d => (ProbeDerivation.result d.probe).output)) =
      some (Chunk.concat sb.output (ProbeDerivation.result d.probe).output hout)
    rw [List.map_append, List.map_singleton]
    exact concatenate_snoc _ _ _ fields.output hout
  · change sb.reads ⊎ FMap.filterKeys (fun q => q ∉ FMap.keys sb.patch)
      (ProbeDerivation.result d.probe).reads = _
    rw [historyReads_snoc, filter_unwritten_eq_restrict, fields.reads, fields.patch, historyPatch_domain]
  · change sb.writes ⊎ FMap.filterKeys (fun q => q ∉ FMap.keys sb.patch)
      (ProbeDerivation.result d.probe).writes = _
    rw [historyWriteDeps_snoc, filter_unwritten_eq_restrict, fields.writes, fields.patch, historyPatch_domain]

/-- An unclosed component's accumulated maps recover both complete paper path sets. -/
theorem HistoryFields.component_paths (trace : Trace m h executor prog) (k : Component)
    (sb : Sandbox sig) (fields : HistoryFields (componentSteps trace k) sb) :
    componentWrites trace k = FMap.dom sb.patch ∧
      componentAccesses trace k = FMap.dom sb.patch ∪ FMap.dom sb.reads ∪ FMap.dom sb.writes := by
  constructor
  · rw [fields.patch, historyPatch_domain]
    rfl
  · rw [fields.patch, fields.reads, fields.writes, historyPatch_domain]
    have ordered : componentAccesses trace k = historyWrites (componentSteps trace k) ∪
        {q | ∃ d ∈ componentSteps trace k,
          q ∈ FMap.dom (ProbeDerivation.result d.probe).reads ∪ FMap.dom (ProbeDerivation.result d.probe).writes} := by
      ext q
      exact or_comm
    exact ordered.trans (history_dependency_envelope _)

/-- A recorded pipeline identity retains the selected slot and probe head. -/
theorem componentAt_pipeline_head (trace : Trace m h executor prog) (pos : Nat)
    (d : StepDerivation m h executor prog) {entry slot : Nat}
    (component : componentAt trace pos d = some (.pipeline entry slot)) :
    ∃ p, d.selection.head = .pipeline p slot := by
  cases head : d.selection.head with
  | standalone p => simp [componentAt, head] at component
  | pipeline p i =>
    cases latest : latestPipeline (trace.take (pos + 1)) with
    | none => simp [componentAt, head, latest] at component
    | some epoch =>
      rcases epoch with ⟨origin, init⟩
      simp only [componentAt, head, latest, Option.map_some, Option.some.injEq,
        Component.pipeline.injEq] at component
      obtain ⟨_, rfl⟩ := component
      exact ⟨p, rfl⟩

end
end IncrPP
end Incr
