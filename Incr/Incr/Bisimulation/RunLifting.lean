import Incr.Incr.Bisimulation.Statements
import Incr.Incr.Bisimulation.Interfaces

/-!
# Prefix and witness bookkeeping for terminating soundness

These helpers restrict an admitted source run to its prefixes and retain
its fixed initial-cache witnesses. They do not assume numbered soundness.
-/

open Incr
namespace Incr.Incr

noncomputable section

variable {sig : Signature} {m : CommandModel sig} {h : Host sig}
  {executor : Executor} {prog : sig.Prog} {start : World sig}

namespace C9

/-- Later steps cannot change an earlier component identity. -/
theorem componentAt_append (xs ys : Trace m h executor prog)
    (pos : Nat) (d : StepDerivation m h executor prog) (hp : pos < xs.length) :
    componentAt (xs ++ ys) pos d = componentAt xs pos d := by
  unfold componentAt
  rw [List.take_append_of_le_length (Nat.succ_le_of_lt hp)]

/-- Component membership retains its original global position. -/
theorem mem_componentSteps_iff {trace : Trace m h executor prog}
    {k : Component} {d : StepDerivation m h executor prog} :
    d ∈ componentSteps trace k ↔
      ∃ pos, (trace)[pos]? = some d ∧ componentAt trace pos d = some k := by
  classical
  constructor
  · intro hd
    obtain ⟨pair, hp, hv⟩ := List.mem_filterMap.mp hd
    obtain ⟨pos, bound, rfl⟩ := List.mem_mapIdx.mp hp
    split_ifs at hv with hk
    have he := Option.some.inj hv
    change (trace)[pos] = d at he
    refine ⟨pos, (List.getElem?_eq_getElem bound).trans (congrArg some he), ?_⟩
    rw [← he]
    exact hk
  · rintro ⟨pos, hd, hk⟩
    obtain ⟨bound, value⟩ := List.getElem?_eq_some_iff.mp hd
    exact List.mem_filterMap.mpr ⟨(componentAt trace pos d, d),
      List.mem_mapIdx.mpr ⟨pos, bound, by simp only [value]⟩, by simp [hk]⟩

/-- An execution extension retains every earlier component step. -/
theorem componentSteps_append_subset (xs ys : Trace m h executor prog) (k : Component) :
    ∀ d ∈ componentSteps xs k, d ∈ componentSteps (xs ++ ys) k := by
  intro d hd
  obtain ⟨pos, get, component⟩ := mem_componentSteps_iff.mp hd
  obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp get
  apply mem_componentSteps_iff.mpr
  exact ⟨pos, (List.getElem?_append_left bound).trans get,
    by rwa [componentAt_append xs ys pos d bound]⟩

/-- Isolation of a whole trace implies isolation of each initial segment. -/
theorem isolated_of_append {xs ys : Trace m h executor prog}
    (isolated : Isolated (xs ++ ys)) : Isolated xs := by
  intro entry i j distinct
  apply Set.disjoint_left.mpr
  intro q written accessed
  apply Set.disjoint_left.mp (isolated entry i j distinct)
  · obtain ⟨d, member, path⟩ := written
    exact ⟨d, componentSteps_append_subset xs ys _ d member, path⟩
  · rcases accessed with dependencies | writes
    · obtain ⟨d, member, path⟩ := dependencies
      exact Or.inl ⟨d, componentSteps_append_subset xs ys _ d member, path⟩
    · obtain ⟨d, member, path⟩ := writes
      exact Or.inr ⟨d, componentSteps_append_subset xs ys _ d member, path⟩

/-- A source run's singleton cache choice supplies fixed initial witnesses. -/
theorem initial_witnesses {pre : Prefix m h executor prog start}
    (consistent : InitialCacheConsistent pre) :
    ∃ witnesses : WitnessMap sig, WitnessesFor m start.cache witnesses ∧
      TimestampCompatible (pre.records ++ witnessRecords witnesses) := by
  obtain ⟨choices, matching, timestamps⟩ := consistent
  cases matching with
  | cons witness rest =>
    rename_i witnesses tail
    cases rest
    have normalized := (prefix_specified_consistent_iff pre [start.cache] [witnesses]).mp timestamps
    refine ⟨witnesses, witness, TimestampCompatible.mono ?_ normalized⟩
    intro x member
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.mem_append] at member ⊢
    exact member.elim Or.inl (fun hm => Or.inr (Or.inr hm))

/-- Fixed admissible witnesses also certify the whole-run cache condition. -/
theorem admissible_initial_cache {witnesses : WitnessMap sig}
    {pre : Prefix m h executor prog start} (chosen : WitnessesFor m start.cache witnesses)
    (admissible : Admissible witnesses pre) : InitialCacheConsistent pre := by
  refine ⟨[witnesses], .cons chosen .nil, ?_⟩
  apply (prefix_specified_consistent_iff pre [start.cache] [witnesses]).mpr
  apply TimestampCompatible.mono ?_ ((pre.paperRecords_witness_consistent_iff witnesses).mp admissible.timestamps)
  intro x member
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.mem_append] at member ⊢
  rcases member with hrecord | hcache | hwitness
  · exact Or.inl hrecord
  · left
    simp only [Prefix.records, worldRecords, List.mem_append]
    exact Or.inl (Or.inl (Or.inr hcache))
  · exact Or.inr hwitness

/-- The record inventory is monotone along an initial trace segment. -/
theorem records_subset {pre full : Prefix m h executor prog start}
    (tail : Trace m h executor prog) (trace : full.trace = pre.trace ++ tail) :
    ∀ x ∈ pre.records, x ∈ full.records := by
  intro x member
  simp only [Prefix.records, List.mem_append, List.mem_flatMap] at member ⊢
  rcases member with initial | ⟨d, hd, record⟩
  · exact Or.inl initial
  · exact Or.inr ⟨d, by rw [trace]; exact List.mem_append_left _ hd, record⟩

/-- Admissibility restricts to an initial segment with the same start. -/
theorem admissible_prefix {witnesses : WitnessMap sig}
    {pre full : Prefix m h executor prog start} (admissible : Admissible witnesses full)
    (tail : Trace m h executor prog) (trace : full.trace = pre.trace ++ tail) :
    Admissible witnesses pre := by
  refine ⟨admissible.operational.of_trace_subset ?_, ?_, ?_⟩
  · intro d hd
    rw [trace]
    exact List.mem_append_left _ hd
  · have isolated := admissible.isolated
    rw [trace] at isolated
    exact isolated_of_append isolated
  · apply (pre.paperRecords_witness_consistent_iff witnesses).mpr
    apply TimestampCompatible.mono ?_ ((full.paperRecords_witness_consistent_iff witnesses).mp admissible.timestamps)
    intro x member
    rcases List.mem_append.mp member with record | witness
    · exact List.mem_append_left _ (records_subset tail trace x record)
    · exact List.mem_append_right _ witness

/-- A terminating source supplies one fixed admissible witness choice. -/
theorem source_witnesses (program : WellFormedProgram m h prog start)
    (source : AdmittedRun m h executor prog start) :
    ∃ witnesses, WitnessesFor m start.cache witnesses ∧
      Admissible witnesses source.run.toPrefix := by
  obtain ⟨witnesses, chosen, timestamps⟩ := initial_witnesses source.cacheConsistent
  exact ⟨witnesses, chosen, source.operational,
    program executor source.run source.operational,
    (source.run.toPrefix.paperRecords_witness_consistent_iff witnesses).mpr timestamps⟩

/-- Fixed source witnesses are consistent with the zero-step records. -/
theorem initial_records {witnesses : WitnessMap sig}
    {pre : Prefix m h executor prog start} (admissible : Admissible witnesses pre) :
    TimestampConsistent (worldPaperRecords start ∪ witnessPaperRecords witnesses) := by
  apply TimestampConsistent.mono ?_ admissible.timestamps
  intro x member
  rcases member with initial | witness
  · exact Or.inl (Or.inl initial)
  · exact Or.inr witness

/-- Connected segments compose without adding a transition. -/
theorem connected_append {a b c : World sig} {xs ys : Trace m h executor prog}
    (left : Connected a xs b) (right : Connected b ys c) : Connected a (xs ++ ys) c := by
  induction left with
  | nil => exact right
  | cons d rest final connected ih => exact .cons d _ _ (ih right)

/-- A connected trace can be split at an arbitrary list boundary. -/
theorem connected_split {a c : World sig} (xs ys : Trace m h executor prog)
    (connected : Connected a (xs ++ ys) c) :
    ∃ b, Connected a xs b ∧ Connected b ys c := by
  induction xs generalizing a with
  | nil => exact ⟨a, .nil a, connected⟩
  | cons d rest ih =>
    cases connected with
    | cons _ _ _ tail =>
      obtain ⟨b, left, right⟩ := ih tail
      exact ⟨b, .cons d _ _ left, right⟩

/-- Empty connected segments have equal endpoints. -/
theorem connected_nil {a c : World sig} (connected : Connected (m := m) (h := h)
    (executor := executor) (prog := prog) a [] c) : a = c := by
  cases connected
  rfl

/-- A final recorded step determines the last boundary and final world. -/
theorem connected_snoc {a c : World sig} (xs : Trace m h executor prog)
    (d : StepDerivation m h executor prog) (connected : Connected a (xs ++ [d]) c) :
    Connected a xs d.before ∧ d.after = c := by
  obtain ⟨b, left, right⟩ := connected_split xs [d] connected
  cases right with
  | cons _ _ _ tail =>
    exact ⟨left, connected_nil tail⟩

/-- A zero-step prefix is exactly the initial prefix. -/
theorem prefix_empty (pre : Prefix m h executor prog start) (trace : pre.trace = []) :
    pre = emptyPrefix m h executor prog start pre.initial := by
  cases pre with
  | mk xs final initial connected =>
    change xs = [] at trace
    subst xs
    cases connected
    rfl

/-- Forward bisimulation lifts every finite admissible Incr prefix. -/
theorem match_incr {witnesses : WitnessMap sig}
    (bisimulation : StrongBisimulation (m := m) (h := h) (prog := prog)
      (start := start) witnesses)
    (pre : Prefix m h .incr prog start) (admissible : Admissible witnesses pre) :
    ∃ vanilla : Prefix m h .vanilla prog start, BisimRelated witnesses pre vanilla := by
  have lift : ∀ xs : Trace m h .incr prog,
      ∀ pre : Prefix m h .incr prog start, pre.trace = xs →
        Admissible witnesses pre →
          ∃ vanilla : Prefix m h .vanilla prog start, BisimRelated witnesses pre vanilla := by
    intro xs
    induction xs using List.reverseRecOn with
    | nil =>
      intro pre trace _
      refine ⟨emptyPrefix m h .vanilla prog start pre.initial, ?_⟩
      rw [prefix_empty pre trace]
      exact bisimulation.2.2.1 pre.initial
    | append_singleton xs d ih =>
      intro pre trace admissible
      obtain ⟨connected, final⟩ := connected_snoc xs d (by simpa only [trace] using pre.connected)
      let previous : Prefix m h .incr prog start := ⟨xs, d.before, pre.initial, connected⟩
      have earlier : Admissible witnesses previous := admissible_prefix admissible [d] trace
      obtain ⟨vanilla, related⟩ := ih previous rfl earlier
      obtain ⟨target, _, matched⟩ := bisimulation.1 previous pre vanilla d.selection.head related
        ⟨earlier, admissible, d, trace, rfl, final, rfl⟩
      exact ⟨target, matched⟩
  exact lift pre.trace pre rfl admissible

/-- Backward bisimulation lifts every finite admissible vanilla prefix. -/
theorem match_vanilla {witnesses : WitnessMap sig}
    (bisimulation : StrongBisimulation (m := m) (h := h) (prog := prog)
      (start := start) witnesses)
    (pre : Prefix m h .vanilla prog start) (admissible : Admissible witnesses pre) :
    ∃ incr : Prefix m h .incr prog start, BisimRelated witnesses incr pre := by
  have lift : ∀ xs : Trace m h .vanilla prog,
      ∀ pre : Prefix m h .vanilla prog start, pre.trace = xs →
        Admissible witnesses pre →
          ∃ incr : Prefix m h .incr prog start, BisimRelated witnesses incr pre := by
    intro xs
    induction xs using List.reverseRecOn with
    | nil =>
      intro pre trace _
      refine ⟨emptyPrefix m h .incr prog start pre.initial, ?_⟩
      rw [prefix_empty pre trace]
      exact bisimulation.2.2.1 pre.initial
    | append_singleton xs d ih =>
      intro pre trace admissible
      obtain ⟨connected, final⟩ := connected_snoc xs d (by simpa only [trace] using pre.connected)
      let previous : Prefix m h .vanilla prog start := ⟨xs, d.before, pre.initial, connected⟩
      have earlier : Admissible witnesses previous := admissible_prefix admissible [d] trace
      obtain ⟨incr, related⟩ := ih previous rfl earlier
      obtain ⟨target, _, matched⟩ := bisimulation.2.1 previous pre incr d.selection.head related
        ⟨earlier, admissible, d, trace, rfl, final, rfl⟩
      exact ⟨target, matched⟩
  exact lift pre.trace pre rfl admissible

end C9

end

end Incr.Incr
