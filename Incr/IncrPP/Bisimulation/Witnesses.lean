import Incr.IncrPP.Preservation.WitnessRecords

/-! # E.10: a local witness consistent with the prefix and fixed initial choices -/
namespace Incr.IncrPP

open Incr
noncomputable section
variable {sig : Signature} {m : CommandModel sig} {h : Host sig}
  {prog : sig.Prog} {start : World sig}

/-- Every memo separately has the printed jointly consistent witness, also after selection. -/
theorem witness_consistency (shape : DenotationShape m) (commands : WellFormedCommands m)
    (host : HostWellFormed m h) (hash : HashInjective m)
    (context : PrefixContext m h prog start) (pre : Prefix m h .live prog start)
    (admissible : Admissible context.witnesses pre) :
    ∀ (b : Boundary pre) key memo, FMap.get b.world.cache key = some memo →
      ∃ fs, EntryWitness m key memo fs ∧
        TimestampConsistent ({recordOfFS fs} ∪ b.paperRecords ∪ witnessPaperRecords context.witnesses) := by
  intro b key memo found
  have preserved := prefixes_and_cache_preservation shape commands host hash pre admissible.operational
    admissible.ordered context.cache context.witnesses context.chosen b
  obtain ⟨fs, witness, provenance⟩ := preserved.memos key memo found
  exact ⟨fs, witness, RecordedWitnessProvenance.consistent_at_boundary host pre admissible.operational b
    context.witnesses admissible.timestamps fs provenance⟩

end
end IncrPP
end Incr
