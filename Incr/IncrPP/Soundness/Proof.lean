import Incr.IncrPP.Soundness.Statements

/-!
# E.12: terminating live soundness

Both source and target are operational terminating runs consistent with their
initial cache. The live run's final cache is well formed in both directions.
All observations retain live/vanilla ordering, including the reverse source
case. This interface does not assert termination or determinism.

`DenotationShape` is the shared model-typing boundary, not a fifth
`def:paper-command-wf` command clause. Its paper-model map remains part of the
transitive exactness review.
The proof lifts the named bisimulation over each separately admitted source run.
-/

namespace Incr.IncrPP

variable {sig : Signature}

/-- E.12, `thm:paper-live-sound`: both admitted terminating directions. -/
theorem thm_sound {m : CommandModel sig} {h : Host sig}
    {prog : sig.Prog} {start : World sig} : SoundnessStatement m h prog start := by
  intro shape commands host hash initial cache program
  constructor
  · intro source
    obtain ⟨witnesses, chosen, consistent⟩ := source.cacheConsistent
    have admitted : Admissible witnesses source.run.toPrefix :=
      ⟨source.operational, program .live source.run source.operational, consistent⟩
    let context : PrefixContext m h prog start :=
      ⟨initial, cache, witnesses, chosen, admitted.initial_consistent⟩
    have bisim := strong_bisimulation shape commands host hash context
    obtain ⟨vanilla, related⟩ := bisim.match_live context source.run.toPrefix admitted
    have completed : h.complete prog vanilla.final := (related.completion host).mp source.run.completion
    let target : AdmittedRun m h .vanilla prog start :=
      ⟨{ toPrefix := vanilla, completion := completed }, related.vanillaAdmissible.operational,
        ⟨witnesses, chosen, related.vanillaAdmissible.timestamps⟩⟩
    have observed := related.observations
    have finalCache := (prefixes_and_cache_preservation shape commands host hash source.run.toPrefix
      source.operational admitted.ordered cache witnesses chosen .final).cache
    exact ⟨target, observed.1, observed.2.1, observed.2.2.1, observed.2.2.2.1,
      observed.2.2.2.2.1, observed.2.2.2.2.2, finalCache⟩
  · intro source
    obtain ⟨witnesses, chosen, consistent⟩ := source.cacheConsistent
    have admitted : Admissible witnesses source.run.toPrefix :=
      ⟨source.operational, program .vanilla source.run source.operational, consistent⟩
    let context : PrefixContext m h prog start :=
      ⟨initial, cache, witnesses, chosen, admitted.initial_consistent⟩
    have bisim := strong_bisimulation shape commands host hash context
    obtain ⟨live, related⟩ := bisim.match_vanilla context source.run.toPrefix admitted
    have completed : h.complete prog live.final := (related.completion host).mpr source.run.completion
    let target : AdmittedRun m h .live prog start :=
      ⟨{ toPrefix := live, completion := completed }, related.liveAdmissible.operational,
        ⟨witnesses, chosen, related.liveAdmissible.timestamps⟩⟩
    have observed := related.observations
    have finalCache := (prefixes_and_cache_preservation shape commands host hash live
      related.liveAdmissible.operational related.liveAdmissible.ordered cache witnesses chosen .final).cache
    exact ⟨target, observed.1, observed.2.1, observed.2.2.1, observed.2.2.2.1,
      observed.2.2.2.2.1, observed.2.2.2.2.2, finalCache⟩

/-- info: 'Incr.IncrPP.thm_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms thm_sound

end IncrPP
end Incr
