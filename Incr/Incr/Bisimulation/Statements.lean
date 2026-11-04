import Incr.Incr.Reuse.Statements

/-!
# Admissible prefix systems and paper bisimulation (`app:bisimulation`)

The relation has the paper's four clauses. Filesystem/cache relations occur
at final worlds, not at every earlier boundary. No stronger internal
simulation invariant is substituted for the paper relation.

O2 reads the `def:paper-bisim-relation` reference to
`lem:paper-buffers`/`lem:paper-sandbox` as their sandbox state/history and
accumulated-result invariants, not both complete lemma packages. The
`thm:paper-bisimulation` proof
identifies these as "sandbox invariants, cache well-formedness and live
cacheable-prefix equations" (`appendix.tex:1426-1429`). It invokes the
`lem:paper-sandbox`
folding clause separately (`appendix.tex:1319-1322`). `RoutingReady` and
`NextCallFolds` therefore remain conclusions of their own lemmas, not fields
of this relation. Alternatives and revisit conditions are recorded in
`docs/recorded-interpretation-decisions.md`.
-/

open Incr
namespace Incr.Incr

noncomputable section

variable {sig : Signature} {m : CommandModel sig} {h : Host sig}
  {executor : Executor} {prog : sig.Prog} {start : World sig}

/-- The raw zero-step prefix. Admissibility is a separate predicate. -/
def emptyPrefix (m : CommandModel sig) (h : Host sig) (executor : Executor)
    (prog : sig.Prog) (start : World sig) (hi : Initial h prog start) :
    Prefix m h executor prog start :=
  ⟨[], start, hi, .nil start⟩

/-- `def:paper-bisim-prefixes`: isolation and consistency with fixed initial
cache witnesses, in addition to the operational execution conditions.
No terminating continuation is required. -/
structure Admissible (witnesses : WitnessMap sig)
    (pre : Prefix m h executor prog start) : Prop where
  operational : Operational pre
  isolated : Isolated pre.trace
  timestamps : TimestampConsistent (pre.paperRecords ∪ witnessPaperRecords witnesses)

/-- One edge of the admissible-prefix system appends one recorded whole step.
Both endpoints are admissible. The label is `p` or `p_i`, represented by `Head`. -/
def PrefixStep (witnesses : WitnessMap sig) (label : Head sig)
    (pre pre' : Prefix m h executor prog start) : Prop :=
  Admissible witnesses pre ∧ Admissible witnesses pre' ∧
    ∃ d, pre'.trace = pre.trace ++ [d] ∧ d.before = pre.final ∧
      d.after = pre'.final ∧ d.selection.head = label

/-- `rel:paper-steps` (clause 1 of `def:paper-bisim-relation`): the returned
output and five control fields
agree before and after probe execution. Entry positions agree by the paired
trace order; initialized probe assignments agree explicitly. -/
def PaperStepsMatch (incr : StepDerivation m h .incr prog)
    (vanilla : StepDerivation m h .vanilla prog) : Prop :=
  incr.out = vanilla.out ∧
    ControlAgree incr.selected vanilla.selected ∧ ControlAgree incr.after vanilla.after ∧
    incr.selection.head = vanilla.selection.head ∧
    incr.selection.init.map (·.probes) = vanilla.selection.init.map (·.probes)

/-- `rel:paper-paths` (clause 4 of `def:paper-bisim-relation`), including
completed invocations. -/
def PathSetsAgree (incr : Trace m h .incr prog) (vanilla : Trace m h .vanilla prog) : Prop :=
  ∀ k, componentWrites incr k = componentWrites vanilla k ∧
    componentAccesses incr k = componentAccesses vanilla k

/-- `def:paper-bisim-relation` (bisimulation relation): the paper relation on
admissible prefixes. The paired-step clause entails equal length. Domain
conditions are fields so an arbitrary use of this relation cannot forget
admissibility. -/
structure BisimRelated (witnesses : WitnessMap sig)
    (incr : Prefix m h .incr prog start) (vanilla : Prefix m h .vanilla prog start) : Prop where
  incrAdmissible : Admissible witnesses incr
  vanillaAdmissible : Admissible witnesses vanilla
  equalLength : incr.trace.length = vanilla.trace.length
  steps : List.Forall₂ PaperStepsMatch incr.trace vanilla.trace
  cache : WellFormedCache m incr.final.cache
  vanillaCache : vanilla.final.cache = start.cache
  sandboxDomains : FMap.dom incr.final.sandbox = FMap.dom vanilla.final.sandbox
  vanillaEmpty : ∀ i sb, FMap.get vanilla.final.sandbox i = some sb →
    sb = Sandbox.initial sb.base
  /-- O2: the `lem:paper-buffers` state/history invariant, without the separate
routing package. -/
  incrSandboxes : SandboxState incr.trace incr.final
  /-- O2: the `lem:paper-sandbox` accumulated-result equation, without the
next-call package. -/
  incrPrefixes : CacheablePrefixes incr.trace incr.final
  disjointPatches : PendingDisjoint incr.final
  overlay : FSApprox vanilla.final.fs (applyPatch incr.final.fs (pendingPatch incr.final))
  paths : PathSetsAgree incr.trace vanilla.trace

/-- `lem:paper-bisim-prefix` clause (i): each current entry has a witness in `F₀`
or an actual retained
filesystem record. Coverage is whole-map membership, not a lossy union of
independent file records. Consistency is stated explicitly as a consequence. -/
def PrefixCacheWitnesses (witnesses : WitnessMap sig)
    (pre : Prefix m h .incr prog start) : Prop :=
  ∀ key memo, FMap.get pre.final.cache key = some memo →
    ∃ (p : sig.Probe) (env : Env sig) (witness : CacheWitness sig),
      Cacheable m p ∧ witness.input.flag = .eof ∧
      key = cacheKey m p env witness.input ∧
      m.denotes p witness.input witness.fs env memo.result ∧
      (recordOfFS witness.fs ∈ witnessPaperRecords witnesses ∨
        recordOfFS witness.fs ∈ pre.paperRecords) ∧
      TimestampConsistent (pre.paperRecords ∪ {recordOfFS witness.fs})

/-- Other components of the same pipeline include closed components. -/
def otherWrites (trace : Trace m h .incr prog) (entry i : Nat) : Set sig.Path :=
  ⋃ j ∈ (Set.univ : Set Nat) \ {i}, componentWrites trace (.pipeline entry j)

/-- `lem:paper-bisim-prefix` clause (ii), including `eq:paper-bisim-frame`. -/
def SliceAt (trace : Trace m h .incr prog) (w : World sig)
    (entry i : Nat) (sb : Sandbox sig) : Prop :=
  componentWrites trace (.pipeline entry i) = FMap.dom sb.patch ∧
    componentAccesses trace (.pipeline entry i) =
      FMap.dom sb.patch ∪ FMap.dom sb.reads ∪ FMap.dom sb.writes ∧
    ∀ Q : Set sig.Path, Disjoint Q (otherWrites trace entry i) → sb.base ↾ Q = w.fs ↾ Q

/-- `lem:paper-bisim-prefix` clause (iii), `eq:paper-bisim-hit-paths`: memo
counting and closing-call counting agree. -/
def HitPathAccounting (trace : Trace m h .incr prog) (k : Component) (sb : Sandbox sig) : Prop :=
  ∀ (d dm : Patch sig) (r rm : Reads sig) (w wm : Writes sig),
    PatchApprox dm (sb.patch ⊎ d) →
    rm = sb.reads ⊎ (r ↾ (Set.univ \ FMap.dom sb.patch)) →
    wm = sb.writes ⊎ (w ↾ (Set.univ \ FMap.dom sb.patch)) →
    componentWrites trace k ∪ FMap.dom dm = componentWrites trace k ∪ FMap.dom d ∧
      componentAccesses trace k ∪ FMap.dom dm ∪ FMap.dom rm ∪ FMap.dom wm =
        componentAccesses trace k ∪ FMap.dom d ∪ FMap.dom r ∪ FMap.dom w

/-- Slice and hit-path properties for every live slot of this world. `current`
can name a just-initialized pipeline with no probe steps yet. -/
def LiveSliceProperties (trace : Trace m h .incr prog) (world : World sig)
    (current : Option (Nat × PipelineInit sig)) : Prop :=
  ∀ i sb, FMap.get world.sandbox i = some sb →
    ∃ entry init, current = some (entry, init) ∧ SliceAt trace world entry i sb ∧
      HitPathAccounting trace (.pipeline entry i) sb

/-- `lem:paper-bisim-prefix` (prefix properties): cache provenance, slices,
frame, and hit paths, including the world immediately after a host selection. -/
def BisimPrefixProperties (witnesses : WitnessMap sig)
    (pre : Prefix m h .incr prog start) : Prop :=
  PrefixCacheWitnesses witnesses pre ∧
    LiveSliceProperties pre.trace pre.final (latestPipeline pre.trace) ∧
    ∀ selection selected, h.select prog pre.final selection selected →
      LiveSliceProperties pre.trace selected (selectedPipeline pre.trace selection)

/-- `thm:paper-bisimulation` (strong bisimulation): both step implications for
the named `def:paper-bisim-relation` relation, initiality, and completion. Main
Theorem 4.3 has a separate existential interface in `MainBisimulation`. -/
def StrongBisimulation (witnesses : WitnessMap sig) : Prop :=
  (∀ (incr incr' : Prefix m h .incr prog start) (vanilla : Prefix m h .vanilla prog start)
      (label : Head sig),
    BisimRelated witnesses incr vanilla → PrefixStep witnesses label incr incr' →
    ∃ vanilla' : Prefix m h .vanilla prog start,
      PrefixStep witnesses label vanilla vanilla' ∧ BisimRelated witnesses incr' vanilla') ∧
  (∀ (vanilla vanilla' : Prefix m h .vanilla prog start) (incr : Prefix m h .incr prog start)
      (label : Head sig),
    BisimRelated witnesses incr vanilla → PrefixStep witnesses label vanilla vanilla' →
    ∃ incr' : Prefix m h .incr prog start,
      PrefixStep witnesses label incr incr' ∧ BisimRelated witnesses incr' vanilla') ∧
  (∀ hi : Initial h prog start,
    BisimRelated witnesses (emptyPrefix m h .incr prog start hi)
      (emptyPrefix m h .vanilla prog start hi)) ∧
  (∀ (incr : Prefix m h .incr prog start) (vanilla : Prefix m h .vanilla prog start),
    BisimRelated witnesses incr vanilla →
    (h.complete prog incr.final ↔ h.complete prog vanilla.final) ∧
      (h.complete prog incr.final → terminal incr.trace = terminal vanilla.trace ∧
        incr.final.ec = vanilla.final.ec ∧ FSApprox incr.final.fs vanilla.final.fs))

end

end Incr.Incr
