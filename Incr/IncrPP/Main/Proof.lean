import Incr.IncrPP.Bisimulation.Proof
import Incr.IncrPP.Main.Preservation
import Incr.IncrPP.Bisimulation.MainObservations

/-!
# Distinct main strong bisimulation: an existential relation

Unlike E.11 this theorem does not prescribe the E.9 relation. Related
prefixes explicitly agree in length and all six step-observation categories.
-/
namespace Incr.IncrPP

open Incr
noncomputable section
variable {sig : Signature} {m : CommandModel sig} {h : Host sig}
  {prog : sig.Prog} {start : World sig}

/-- Main prefix-system zero-state membership is its own statement obligation. -/
theorem main_zero_admissible (context : PrefixContext m h prog start) (executor : Executor) :
    MainAdmissible context.witnesses (zeroPrefix (m := m) executor context.initial) := by
  have zero := zero_admissible context executor
  exact ⟨zero.operational, zero.ordered, zero.timestamps⟩

def mainZeroState (context : PrefixContext m h prog start) (executor : Executor) :
    (mainPrefixSystem executor context).State :=
  ⟨zeroPrefix executor context.initial, main_zero_admissible context executor⟩

/-- External supplies and consumed chunks are separate conjuncts of `SameSuppliedInputs`. -/
def StepObservations (live : Trace m h .live prog) (vanilla : Trace m h .vanilla prog) : Prop :=
  SameProbeSchedule live vanilla ∧ SameEnvironments live vanilla ∧ SameSuppliedInputs live vanilla ∧
    live.map (fun d => ProbeDerivation.produced d.probe) =
      vanilla.map (fun d => ProbeDerivation.produced d.probe) ∧
    live.map (fun d => d.out) = vanilla.map (fun d => d.out)

/-- Every printed conclusion for the existential main-text relation. -/
structure MainBisimulationProperties (context : PrefixContext m h prog start)
    (relation : (mainPrefixSystem .live context).State →
      (mainPrefixSystem .vanilla context).State → Prop) : Prop where
  bisimulation : StrongBisimulation (mainPrefixSystem .live context)
    (mainPrefixSystem .vanilla context) relation
  initial : relation (mainZeroState context .live) (mainZeroState context .vanilla)
  observations : ∀ live vanilla, relation live vanilla →
    (PrefixComplete live.val ∨ PrefixComplete vanilla.val) → CompleteObservations live.val vanilla.val
  length : ∀ live vanilla, relation live vanilla → live.val.trace.length = vanilla.val.trace.length
  steps : ∀ live vanilla, relation live vanilla → StepObservations live.val.trace vanilla.val.trace

/-- The distinct main admissibility package entails the appendix package on the same prefix. -/
theorem MainAdmissible.to_appendix {executor : Executor} {witnesses : WitnessMap sig}
    {pre : Prefix m h executor prog start} (admissible : MainAdmissible witnesses pre) : Admissible witnesses pre :=
  ⟨admissible.operational, admissible.ordered, admissible.timestamps⟩

/-- The appendix admissibility package entails the distinct main package on the same prefix. -/
theorem Admissible.to_main {executor : Executor} {witnesses : WitnessMap sig}
    {pre : Prefix m h executor prog start} (admissible : Admissible witnesses pre) : MainAdmissible witnesses pre :=
  ⟨admissible.operational, admissible.ordered, admissible.timestamps⟩

/-- `thm:main-live-bisim`, with an existential relation, not an alias of E.11. -/
theorem main_strong_bisimulation (shape : DenotationShape m) (commands : WellFormedCommands m)
    (host : HostWellFormed m h) (hash : HashInjective m)
    (context : PrefixContext m h prog start) :
    ∃ relation : (mainPrefixSystem .live context).State →
        (mainPrefixSystem .vanilla context).State → Prop,
      MainBisimulationProperties context relation := by
  let relation : (mainPrefixSystem .live context).State → (mainPrefixSystem .vanilla context).State → Prop :=
    fun live vanilla => Correspondence context live.val vanilla.val
  have bisim := strong_bisimulation shape commands host hash context
  refine ⟨relation, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · intro live vanilla related label live' edge
      obtain ⟨old, next, d, before, head, trace, after⟩ := edge
      let left : (prefixSystem .live context).State := ⟨live.val, old.to_appendix⟩
      let right : (prefixSystem .vanilla context).State := ⟨vanilla.val, vanilla.property.to_appendix⟩
      let left' : (prefixSystem .live context).State := ⟨live'.val, next.to_appendix⟩
      have appendixEdge : (prefixSystem .live context).step left label left' :=
        ⟨old.to_appendix, next.to_appendix, d, before, head, trace, after⟩
      obtain ⟨other, targetEdge, targetRelated⟩ :=
        bisim.bisimulation.forward left right related label left' appendixEdge
      let target : (mainPrefixSystem .vanilla context).State := ⟨other.val, other.property.to_main⟩
      refine ⟨target, ?_, targetRelated⟩
      obtain ⟨targetOld, targetNext, td, tb, th, tt, ta⟩ := targetEdge
      exact ⟨targetOld.to_main, targetNext.to_main, td, tb, th, tt, ta⟩
    · intro live vanilla related label vanilla' edge
      obtain ⟨old, next, d, before, head, trace, after⟩ := edge
      let left : (prefixSystem .live context).State := ⟨live.val, live.property.to_appendix⟩
      let right : (prefixSystem .vanilla context).State := ⟨vanilla.val, old.to_appendix⟩
      let right' : (prefixSystem .vanilla context).State := ⟨vanilla'.val, next.to_appendix⟩
      have appendixEdge : (prefixSystem .vanilla context).step right label right' :=
        ⟨old.to_appendix, next.to_appendix, d, before, head, trace, after⟩
      obtain ⟨other, targetEdge, targetRelated⟩ :=
        bisim.bisimulation.backward left right related label right' appendixEdge
      let target : (mainPrefixSystem .live context).State := ⟨other.val, other.property.to_main⟩
      refine ⟨target, ?_, targetRelated⟩
      obtain ⟨targetOld, targetNext, td, tb, th, tt, ta⟩ := targetEdge
      exact ⟨targetOld.to_main, targetNext.to_main, td, tb, th, tt, ta⟩
    · intro live vanilla related
      exact Correspondence.completion host related
  · exact zero_correspondence context
  · intro live vanilla related _
    exact Correspondence.observations related
  · intro live vanilla related
    exact related.length
  · intro live vanilla related
    obtain ⟨schedule, environments, supplied⟩ := related.input_observations
    obtain ⟨produced, returned⟩ := matching_produced_returned related.matchingSteps
    exact ⟨schedule, environments, supplied, produced, returned⟩

end
end IncrPP
end Incr
