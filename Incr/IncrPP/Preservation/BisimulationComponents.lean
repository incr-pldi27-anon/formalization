import Incr.IncrPP.Bisimulation.MatchingObservations
import Incr.IncrPP.WellFormedness.ComponentRepresentation
import Incr.IncrPP.Preservation.BisimulationMath

/-!
# Matching component identities

The host compares initialization presence and ordered probe assignments,
not the identity of complete initialization or delivery annotations.
-/

namespace Incr.IncrPP

noncomputable section

variable {sig : Signature} {m : CommandModel sig} {h : Host sig} {prog : sig.Prog}

/-- Matching initializations allocate exactly the same ordered slot indices. -/
theorem MatchingProbeSteps.initial_slot {live : StepDerivation m h .live prog}
    {vanilla : StepDerivation m h .vanilla prog} (matched : MatchingProbeSteps live vanilla) (slot : Nat) :
    (∃ init, live.selection.init = some init ∧ slot < init.probes.length) ↔
      ∃ init, vanilla.selection.init = some init ∧ slot < init.probes.length := by
  have same := matched.2.2.2.2
  cases hl : live.selection.init <;> cases hr : vanilla.selection.init <;> simp_all

/-- At each original position, the matching relation supplies both retained derivations. -/
theorem matching_at_position {live : Trace m h .live prog} {vanilla : Trace m h .vanilla prog}
    (matched : List.Forall₂ MatchingProbeSteps live vanilla) (pos : Nat)
    (d : StepDerivation m h .live prog) (atPos : (live)[pos]? = some d) :
    ∃ other, (vanilla)[pos]? = some other ∧ MatchingProbeSteps d other := by
  obtain ⟨bound, eq⟩ := List.getElem?_eq_some_iff.mp atPos
  have lengthEq := matched.length_eq
  have otherBound : pos < vanilla.length := by rw [← lengthEq]; exact bound
  refine ⟨(vanilla)[pos], List.getElem?_eq_getElem otherBound, ?_⟩
  have same := matched.get bound otherBound
  simpa [eq] using same

/-- Matched initialization assignments and standalone heads give exactly the same component domain. -/
theorem matching_componentDomain {live : Trace m h .live prog} {vanilla : Trace m h .vanilla prog}
    (matched : List.Forall₂ MatchingProbeSteps live vanilla) : componentDomain live = componentDomain vanilla := by
  ext k
  constructor
  · rintro ⟨pos, d, atPos, kind⟩
    obtain ⟨other, otherAt, step⟩ := matching_at_position matched pos d atPos
    refine ⟨pos, other, otherAt, ?_⟩
    rcases kind with ⟨p, head, equal⟩ | ⟨init, slot, initializes, bound, equal⟩
    · exact Or.inl ⟨p, step.1.symm.trans head, equal⟩
    · obtain ⟨otherInit, otherInitAt, otherBound⟩ := (step.initial_slot slot).mp ⟨init, initializes, bound⟩
      exact Or.inr ⟨otherInit, slot, otherInitAt, otherBound, equal⟩
  · rintro ⟨pos, d, atPos, kind⟩
    have lengthEq := matched.length_eq
    have bound := (List.getElem?_eq_some_iff.mp atPos).choose
    have liveBound : pos < live.length := by rw [lengthEq]; exact bound
    let other := (live)[pos]
    have otherAt : (live)[pos]? = some other := List.getElem?_eq_getElem liveBound
    obtain ⟨step, stepAt, related⟩ := matching_at_position matched pos other otherAt
    rw [atPos] at stepAt
    cases Option.some.inj stepAt
    refine ⟨pos, other, otherAt, ?_⟩
    rcases kind with ⟨p, head, equal⟩ | ⟨init, slot, initializes, domain, equal⟩
    · exact Or.inl ⟨p, related.1.trans head, equal⟩
    · obtain ⟨otherInit, otherInitAt, otherBound⟩ := (related.initial_slot slot).mpr ⟨init, initializes, domain⟩
      exact Or.inr ⟨otherInit, slot, otherInitAt, otherBound, equal⟩

/-- The last true marker's original zero-based position. -/
def lastInitMarker (markers : List Bool) : Option Nat :=
  ((markers.mapIdx fun pos flag => if flag then some pos else none).filterMap id).getLast?

/-- Appending a marker updates the last-initialization index exactly when it is true. -/
theorem lastInitMarker_snoc (markers : List Bool) (flag : Bool) :
    lastInitMarker (markers ++ [flag]) = if flag then some markers.length else lastInitMarker markers := by
  cases flag <;> simp [lastInitMarker, List.mapIdx_concat, List.filterMap_append]

/-- A trace's current pipeline index depends only on initialization presence, not annotations. -/
theorem latestPipeline_index_markers {executor : Executor} (trace : Trace m h executor prog) :
    (latestPipeline trace).map Prod.fst = lastInitMarker (trace.map (fun d => d.selection.init.isSome)) := by
  induction trace using List.reverseRecOn with
  | nil => rfl
  | append_singleton trace d ih =>
    rw [latestPipeline_snoc, List.map_append, List.map_singleton, lastInitMarker_snoc]
    cases initialized : d.selection.init <;> simp [ih]

/-- Matching initial assignments give identical initialization-presence markers. -/
theorem matching_init_markers {live : Trace m h .live prog} {vanilla : Trace m h .vanilla prog}
    (matched : List.Forall₂ MatchingProbeSteps live vanilla) :
    live.map (fun d => d.selection.init.isSome) = vanilla.map (fun d => d.selection.init.isSome) := by
  induction matched with
  | nil => rfl
  | @cons l r left right step rest ih =>
    have init := step.2.2.2.2
    cases hl : l.selection.init <;> cases hr : r.selection.init <;>
      simp_all

/-- Matched traces have the same current initialization index. -/
theorem matching_latestPipeline_index {live : Trace m h .live prog} {vanilla : Trace m h .vanilla prog}
    (matched : List.Forall₂ MatchingProbeSteps live vanilla) :
    (latestPipeline live).map Prod.fst = (latestPipeline vanilla).map Prod.fst := by
  rw [latestPipeline_index_markers, latestPipeline_index_markers, matching_init_markers matched]

/-- Matching prefixes have the same current component identity at each slot. -/
theorem matching_liveComponent {live : Trace m h .live prog} {vanilla : Trace m h .vanilla prog}
    (matched : List.Forall₂ MatchingProbeSteps live vanilla) (slot : Nat) :
    liveComponent live slot = liveComponent vanilla slot := by
  unfold liveComponent
  have equal := matching_latestPipeline_index matched
  cases hl : latestPipeline live with
  | none =>
    cases hr : latestPipeline vanilla with
    | none => rfl
    | some entry => simp [hl, hr] at equal
  | some a =>
    cases hr : latestPipeline vanilla with
    | none => simp [hl, hr] at equal
    | some b =>
      have first : a.1 = b.1 := by simpa [hl, hr] using equal
      simp [first]

/-- Matched derivations at an original position have the same component identity. -/
theorem matching_componentAt {live : Trace m h .live prog} {vanilla : Trace m h .vanilla prog}
    (matched : List.Forall₂ MatchingProbeSteps live vanilla) (pos : Nat)
    (d : StepDerivation m h .live prog) (other : StepDerivation m h .vanilla prog)
    (step : MatchingProbeSteps d other) : componentAt live pos d = componentAt vanilla pos other := by
  have prefixes := List.forall₂_take (pos + 1) matched
  cases head : d.selection.head with
  | standalone p => simp [componentAt, head, ← step.1]
  | pipeline p slot =>
    have identities := matching_liveComponent prefixes slot
    simpa [componentAt, liveComponent, head, ← step.1] using identities

/-- Matched traces have the same chronological closing positions for every component. -/
theorem matching_closingPositions {live : Trace m h .live prog} {vanilla : Trace m h .vanilla prog}
    (matched : List.Forall₂ MatchingProbeSteps live vanilla) (k : Component) :
    closingPositions live k = closingPositions vanilla k := by
  classical
  have indexed :
      live.mapIdx (fun pos d => if componentAt live pos d = some k ∧
        (ProbeDerivation.input d.probe).flag = .eof then some (paperPosition pos) else none) =
      vanilla.mapIdx (fun pos d => if componentAt vanilla pos d = some k ∧
        (ProbeDerivation.input d.probe).flag = .eof then some (paperPosition pos) else none) := by
    apply List.ext_getElem?
    intro pos
    simp only [List.getElem?_mapIdx]
    cases atLeft : (live)[pos]? with
    | none =>
      have outside : live.length ≤ pos := List.getElem?_eq_none_iff.mp atLeft
      have otherOutside : vanilla.length ≤ pos := by rwa [← matched.length_eq]
      have atRight : (vanilla)[pos]? = none := List.getElem?_eq_none_iff.mpr otherOutside
      simp [atRight]
    | some d =>
      obtain ⟨other, atRight, step⟩ := matching_at_position matched pos d atLeft
      simp only [atRight, Option.map_some]
      rw [matching_componentAt matched pos d other step, step.inputs]
  unfold closingPositions
  rw [indexed]

/-- Matched traces have identical history-based live pipeline components. -/
theorem matching_liveComponents {live : Trace m h .live prog} {vanilla : Trace m h .vanilla prog}
    (matched : List.Forall₂ MatchingProbeSteps live vanilla) : LiveComponentsCorrespond live vanilla := by
  intro entry slot
  unfold LivePipelineComponent
  rw [matching_componentDomain matched, matching_closingPositions matched]

/-- Matched components have the same actual closing position or open endpoint. -/
theorem matching_lastPosition {live : Trace m h .live prog} {vanilla : Trace m h .vanilla prog}
    (matched : List.Forall₂ MatchingProbeSteps live vanilla) (k : Component) :
    lastPosition live k = lastPosition vanilla k := by
  simp only [lastPosition, matching_closingPositions matched, matched.length_eq]

/-- E.9's matched components and equal controls enable host selections in both directions. -/
theorem Correspondence.selection_transport {start : World sig} (host : HostWellFormed m h)
    {context : PrefixContext m h prog start}
    {live : Prefix m h .live prog start} {vanilla : Prefix m h .vanilla prog start}
    (related : Correspondence context live vanilla) (control : ControlAgree live.final vanilla.final) :
    SelectionsTransport h prog live.final vanilla.final ∧ SelectionsTransport h prog vanilla.final live.final := by
  exact host.selectionCongruence prog start start live vanilla related.liveAdmissible.operational
    related.vanillaAdmissible.operational (matching_liveComponents related.matchingSteps) control related.filesystem

end
end IncrPP
end Incr
