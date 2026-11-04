import Incr.IncrPP.Bisimulation.Witnesses
import Incr.IncrPP.Bisimulation.MatchingObservations
import Incr.IncrPP.Reuse.HitCases

/-!
# E.11: the named relation is a strong bisimulation

The transition systems fix the same initial witnesses. The histories need
not be jointly consistent with each other. Zero prefixes, completion, and
complete observations are explicit, in addition to both step directions.
-/
namespace Incr.IncrPP

open Incr
noncomputable section
variable {sig : Signature} {m : CommandModel sig} {h : Host sig}
  {prog : sig.Prog} {start : World sig}

def zeroPrefix (executor : Executor) (initial : Initial h prog start) :
    Prefix m h executor prog start :=
  ⟨[], start, initial, .nil start⟩

/-- The initial state belongs to each fixed-witness prefix system. -/
theorem zero_admissible (context : PrefixContext m h prog start) (executor : Executor) :
    Admissible context.witnesses (zeroPrefix (m := m) executor context.initial) := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro d member
      simp [zeroPrefix] at member
    · intro n bound
      have initial : TimestampConsistent (worldPaperRecords start) :=
        TimestampConsistent.mono Set.subset_union_left context.consistent
      simpa [zeroPrefix, tracePaperRecords] using initial
  · intro entry i j member
    simp [zeroPrefix, componentDomain] at member
  · simpa [zeroPrefix, Prefix.paperRecords, tracePaperRecords] using context.consistent

def zeroState (context : PrefixContext m h prog start) (executor : Executor) :
    (prefixSystem executor context).State :=
  ⟨zeroPrefix executor context.initial, zero_admissible context executor⟩

/-- Step matching and completion for an arbitrary relation on two labeled systems. -/
structure StrongBisimulation (left right : PrefixSystem sig)
    (relation : left.State → right.State → Prop) : Prop where
  forward : ∀ x y, relation x y → ∀ label x', left.step x label x' →
    ∃ y', right.step y label y' ∧ relation x' y'
  backward : ∀ x y, relation x y → ∀ label y', right.step y label y' →
    ∃ x', left.step x label x' ∧ relation x' y'
  completion : ∀ x y, relation x y → (left.complete x ↔ right.complete y)

/-- All terminating observations, in live/vanilla order. -/
def CompleteObservations (live : Prefix m h .live prog start)
    (vanilla : Prefix m h .vanilla prog start) : Prop :=
  SameProbeSchedule live.trace vanilla.trace ∧ SameEnvironments live.trace vanilla.trace ∧
    SameSuppliedInputs live.trace vanilla.trace ∧ terminal live.trace = terminal vanilla.trace ∧
    live.final.ec = vanilla.final.ec ∧ FSApprox live.final.fs vanilla.final.fs

/-- E.9 restricted to the exact E.8 system state types. -/
def correspondenceRelation (context : PrefixContext m h prog start) :
    (prefixSystem .live context).State → (prefixSystem .vanilla context).State → Prop :=
  fun live vanilla => Correspondence context live.val vanilla.val

/-- The two actual empty prefixes satisfy every clause of the named correspondence. -/
theorem zero_correspondence (context : PrefixContext m h prog start) :
    correspondenceRelation context (zeroState context .live) (zeroState context .vanilla) := by
  refine ⟨zero_admissible context .live, zero_admissible context .vanilla, rfl, ?_, ?_, ?_, ?_⟩
  · exact List.Forall₂.nil
  · refine ⟨?_, rfl, rfl, ?_, ?_⟩
    · exact context.cache
    · intro entry i sb live found
      simp [zeroState, zeroPrefix, context.initial.2.1, FMap.get] at found
    · intro entry i sb live found
      simp [zeroState, zeroPrefix, context.initial.2.1, FMap.get] at found
  · exact FSApprox.of_contents (fun _ => rfl)
  · intro j bound k liveDomain vanillaDomain
    simp [zeroState, zeroPrefix, componentDomain] at liveDomain

/-- Matched connected steps preserve final control agreement. -/
theorem MatchingProbeSteps.connected_control
    {left : Trace m h .live prog} {right : Trace m h .vanilla prog}
    (matched : List.Forall₂ MatchingProbeSteps left right)
    {leftStart leftEnd rightStart rightEnd : World sig}
    (initial : ControlAgree leftStart rightStart)
    (leftConnected : Connected leftStart left leftEnd)
    (rightConnected : Connected rightStart right rightEnd) : ControlAgree leftEnd rightEnd := by
  induction matched generalizing leftStart rightStart with
  | nil =>
    cases leftConnected
    cases rightConnected
    exact initial
  | cons headMatch tailMatch ih =>
    cases leftConnected with
    | cons _ _ _ leftTail =>
      cases rightConnected with
      | cons _ _ _ rightTail =>
        exact ih headMatch.2.2.2.1 leftTail rightTail

/-- E.9's matched trace supplies equal final control fields. -/
theorem Correspondence.control {context : PrefixContext m h prog start}
    {live : Prefix m h .live prog start} {vanilla : Prefix m h .vanilla prog start}
    (related : Correspondence context live vanilla) : ControlAgree live.final vanilla.final := by
  apply MatchingProbeSteps.connected_control related.matchingSteps ?_ live.connected vanilla.connected
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- E.9 preserves and reflects completion without requiring a future step. -/
theorem Correspondence.completion (host : HostWellFormed m h)
    {context : PrefixContext m h prog start}
    {live : Prefix m h .live prog start} {vanilla : Prefix m h .vanilla prog start}
    (related : Correspondence context live vanilla) : PrefixComplete live ↔ PrefixComplete vanilla := by
  have control := related.control
  constructor
  · intro complete
    have emptyLive := host.completionEmpty prog live.final complete
    have emptyVanillaBuffers : vanilla.final.buffer = ∅ := by rw [← control.2.2.2.1, emptyLive.1]
    have emptyVanillaSandboxes : vanilla.final.sandbox = ∅ := by
      apply FMap.eq_empty_of_dom_eq_empty
      rw [← related.cacheAndSandboxes.domains, emptyLive.2, FMap.dom_empty]
    exact (host.completionInvariance prog live.final vanilla.final emptyLive.1 emptyLive.2
      emptyVanillaBuffers emptyVanillaSandboxes control.1 control.2.1 control.2.2.1 control.2.2.2.2
      related.filesystem).mp complete
  · intro complete
    have emptyVanilla := host.completionEmpty prog vanilla.final complete
    have emptyLiveBuffers : live.final.buffer = ∅ := by rw [control.2.2.2.1, emptyVanilla.1]
    have emptyLiveSandboxes : live.final.sandbox = ∅ := by
      apply FMap.eq_empty_of_dom_eq_empty
      rw [related.cacheAndSandboxes.domains, emptyVanilla.2, FMap.dom_empty]
    exact (host.completionInvariance prog live.final vanilla.final emptyLiveBuffers emptyLiveSandboxes
      emptyVanilla.1 emptyVanilla.2 control.1 control.2.1 control.2.2.1 control.2.2.2.2
      related.filesystem).mpr complete

/-- Every related pair already satisfies the complete observation package. -/
theorem Correspondence.observations {context : PrefixContext m h prog start}
    {live : Prefix m h .live prog start} {vanilla : Prefix m h .vanilla prog start}
    (related : Correspondence context live vanilla) : CompleteObservations live vanilla := by
  obtain ⟨schedule, environments, inputs⟩ := related.input_observations
  exact ⟨schedule, environments, inputs, matching_terminal related.matchingSteps,
    related.control.2.1, related.filesystem⟩

/-- E.11 retains its named relation rather than existentially replacing it. -/
structure BisimulationStatement (context : PrefixContext m h prog start) : Prop where
  bisimulation : StrongBisimulation (prefixSystem .live context) (prefixSystem .vanilla context)
    (correspondenceRelation context)
  initial : correspondenceRelation context (zeroState context .live) (zeroState context .vanilla)
  observations : ∀ live vanilla, correspondenceRelation context live vanilla →
    (PrefixComplete live.val ∨ PrefixComplete vanilla.val) → CompleteObservations live.val vanilla.val

/-- E.11, with all printed model/host/hash and fixed initial context assumptions. -/
theorem strong_bisimulation (shape : DenotationShape m) (commands : WellFormedCommands m)
    (host : HostWellFormed m h) (hash : HashInjective m)
    (context : PrefixContext m h prog start) : BisimulationStatement context := by
  constructor
  · constructor
    · intro x y relation label x' edge
      obtain ⟨_, liveAdmissible, d, before, labelEq, joined, after⟩ := edge
      have related : Correspondence context x.val y.val := relation
      have matchStep : ∃ target : Prefix m h .vanilla prog start,
          PrefixStep context.witnesses d.selection.head y.val target ∧ Correspondence context x'.val target := by
        cases call : LiveDerivation.callFS d.probe with
        | none =>
          exact related.forward_hit shape commands host hash related.control d before joined after liveAdmissible call
        | some fs =>
          have same := d.probe.callFS_some call
          subst fs
          exact related.forward_executing commands shape host hash related.control d before joined after liveAdmissible call
      obtain ⟨target, targetEdge, targetRelated⟩ := matchStep
      let state : (prefixSystem .vanilla context).State := ⟨target, targetEdge.2.1⟩
      refine ⟨state, ?_, targetRelated⟩
      change PrefixStep context.witnesses label y.val target
      simpa only [labelEq] using targetEdge
    · intro x y relation label y' edge
      obtain ⟨_, vanillaAdmissible, d, before, labelEq, joined, after⟩ := edge
      have related : Correspondence context x.val y.val := relation
      obtain ⟨target, targetEdge, targetRelated⟩ :=
        related.backward_executing commands shape host hash related.control d before joined after vanillaAdmissible
      let state : (prefixSystem .live context).State := ⟨target, targetEdge.2.1⟩
      refine ⟨state, ?_, targetRelated⟩
      change PrefixStep context.witnesses label x.val target
      simpa only [labelEq] using targetEdge
    · intro x y relation
      exact Correspondence.completion host relation
  · exact zero_correspondence context
  · intro live vanilla related _
    exact Correspondence.observations related

end
end IncrPP
end Incr
