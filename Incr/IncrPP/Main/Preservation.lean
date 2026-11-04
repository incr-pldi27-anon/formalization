import Incr.IncrPP.Reuse.HitPrelude
import Incr.IncrPP.Main.Statements

/-! # Distinct main prefix lemma: a base filesystem and its absorption equation -/
namespace Incr.IncrPP

open Incr
noncomputable section
variable {sig : Signature} {m : CommandModel sig} {h : Host sig}
  {prog : sig.Prog} {start : World sig}

/-- Main-text package, not the stronger appendix repair/provenance package. -/
structure MainPrefixProperties (pre : Prefix m h .live prog start) (b : Boundary pre) : Prop where
  cache : WellFormedCache m b.world.cache
  firstEnvironment : ∀ entry i p sb, b.livePipeline entry i → b.assigned entry i p → Cacheable m p →
    FMap.get b.world.sandbox i = some sb → openSteps pre.trace (.pipeline entry i) ≠ [] →
      ∃ env, FirstEnvironment pre.trace (.pipeline entry i) env
  entries : ∀ entry i p sb, b.livePipeline entry i → b.assigned entry i p → Cacheable m p →
    FMap.get b.world.sandbox i = some sb → openSteps pre.trace (.pipeline entry i) ≠ [] →
    ∀ env, FirstEnvironment pre.trace (.pipeline entry i) env →
      ∃ base, m.denotes p sb.input base env (prefixResult sb) ∧
        applyPatch base sb.patch = b.world.fs

/-- `lem:main-live-prefix`: endpoint and post-selection, without fixed witness parameters. -/
theorem main_prefixes_and_cache_preservation (shape : DenotationShape m)
    (commands : WellFormedCommands m) (host : HostWellFormed m h) (hash : HashInjective m)
    (pre : Prefix m h .live prog start) (operational : Operational pre)
    (ordered : MainExitOrdered pre.trace) (cache : WellFormedCache m start.cache) :
    ∀ b : Boundary pre, MainPrefixProperties pre b := by
  obtain ⟨witnesses, chosen⟩ := WellFormedCache.exists_witnesses start.cache cache
  have preserved := prefixes_and_cache_preservation shape commands host hash pre operational ordered cache witnesses chosen
  intro b
  refine ⟨(preserved b).cache, ?_, ?_⟩
  · intro entry i p sb live assigned cacheable present progressed
    exact ((preserved b).entries entry i p sb live assigned cacheable present).firstEnvironment progressed
  · intro entry i p sb live assigned cacheable present progressed env first
    obtain ⟨repair, repaired⟩ :=
      ((preserved b).entries entry i p sb live assigned cacheable present).progressed progressed env first
    refine ⟨applyPatch b.world.fs repair, repaired.denotation, ?_⟩
    have absorbed := Operational.liveAbsorbed host pre operational ordered b entry i sb live present
    rw [patch_absorption b.world.fs repair sb.patch (by rw [repaired.domain]), absorbed]

end
end IncrPP
end Incr
