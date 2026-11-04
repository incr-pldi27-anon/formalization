import Incr.IncrPP.Preservation.Proof
import Incr.IncrPP.Bisimulation.PrefixSystems

/-!
# E.9: named live correspondence

The relation contains four printed clauses plus its admissibility and
length domain. G1 embeds entry-local E.4/E.6 only; global routing, closing
order, and all-memo provenance are not hidden relation fields.
-/
namespace Incr.IncrPP

open Incr
noncomputable section
variable {sig : Signature} {m : CommandModel sig} {h : Host sig}
  {prog : sig.Prog} {start : World sig}

/-- Corresponding probe judgments, their control frames, and initialization assignments. -/
def MatchingProbeSteps (live : StepDerivation m h .live prog)
    (vanilla : StepDerivation m h .vanilla prog) : Prop :=
  live.selection.head = vanilla.selection.head ∧ live.out = vanilla.out ∧
    ControlAgree live.selected vanilla.selected ∧ ControlAgree live.after vanilla.after ∧
    live.selection.init.map (·.probes) = vanilla.selection.init.map (·.probes)

/-- Fixed snapshots, E.4 open histories/path sets, and the cacheable E.6 entry package. -/
structure LiveEntryProperties (pre : Prefix m h .live prog start) (entry i : Nat)
    (sb : Sandbox sig) : Prop where
  snapshot : ∃ fs init, (Boundary.final (pre := pre)).entry entry = some (fs, init) ∧ sb.base = fs
  history : EntryHistory pre.trace entry i sb
  cacheable : ∀ p, (Boundary.final (pre := pre)).assigned entry i p → Cacheable m p →
    EntryPrefix pre .final entry i p sb

/-- Clause 2 keeps its cache and domain equations explicit. -/
structure CacheAndSandboxes (live : Prefix m h .live prog start)
    (vanilla : Prefix m h .vanilla prog start) : Prop where
  liveCache : WellFormedCache m live.final.cache
  vanillaCache : vanilla.final.cache = start.cache
  domains : FMap.dom live.final.sandbox = FMap.dom vanilla.final.sandbox
  vanillaEntries : ∀ entry i sb, (Boundary.final (pre := vanilla)).livePipeline entry i →
    FMap.get vanilla.final.sandbox i = some sb →
      ∃ fs init, (Boundary.final (pre := vanilla)).entry entry = some (fs, init) ∧ sb = Sandbox.initial fs
  liveEntries : ∀ entry i sb, (Boundary.final (pre := live)).livePipeline entry i →
    FMap.get live.final.sandbox i = some sb → LiveEntryProperties live entry i sb

/-- Clause 4 compares every retained prefix, not just final path unions. -/
def PathsAtEveryPrefix (live : Trace m h .live prog) (vanilla : Trace m h .vanilla prog) : Prop :=
  ∀ j, j ≤ live.length → ∀ k,
    k ∈ componentDomain (live.take j) → k ∈ componentDomain (vanilla.take j) →
      componentWrites (live.take j) k = componentWrites (vanilla.take j) k ∧
        componentAccesses (live.take j) k = componentAccesses (vanilla.take j) k

/-- E.9, with its explicit admissible/equal-length domain and four numbered clauses. -/
structure Correspondence (context : PrefixContext m h prog start)
    (live : Prefix m h .live prog start) (vanilla : Prefix m h .vanilla prog start) : Prop where
  liveAdmissible : Admissible context.witnesses live
  vanillaAdmissible : Admissible context.witnesses vanilla
  length : live.trace.length = vanilla.trace.length
  matchingSteps : List.Forall₂ MatchingProbeSteps live.trace vanilla.trace
  cacheAndSandboxes : CacheAndSandboxes live vanilla
  filesystem : FSApprox live.final.fs vanilla.final.fs
  paths : PathsAtEveryPrefix live.trace vanilla.trace

end
end IncrPP
end Incr
