import Incr.Incr.Bisimulation.Observations
import Incr.Incr.Preservation.Proof

/-! # Initiality and completion for the recorded `thm:paper-bisimulation` relation -/

open Incr
namespace Incr.Incr.BisimulationBasis

noncomputable section

variable {sig : Signature} {m : CommandModel sig} {h : Host sig}
  {prog : sig.Prog} {start : World sig}

private theorem connected_control
    {left : Trace m h .incr prog} {right : Trace m h .vanilla prog}
    (matched : List.Forall₂ PaperStepsMatch left right)
    {wl wr fl fr : World sig} (cl : Connected wl left fl) (cr : Connected wr right fr)
    (before : ControlAgree wl wr) : ControlAgree fl fr := by
  induction matched generalizing wl wr with
  | nil =>
    cases cl
    cases cr
    exact before
  | @cons dl dr left right step rest ih =>
    cases cl
    cases cr
    exact ih (by assumption) (by assumption) step.2.2.1

/-- Matched connected prefixes agree on their final control fields. -/
theorem final_control {witnesses : WitnessMap sig}
    {incr : Prefix m h .incr prog start} {vanilla : Prefix m h .vanilla prog start}
    (related : BisimRelated witnesses incr vanilla) : ControlAgree incr.final vanilla.final :=
  connected_control related.steps incr.connected vanilla.connected ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- No live sandbox means that the pending overlay is empty. -/
theorem pending_empty {w : World sig} (empty : w.sandbox = ∅) : pendingPatch w = ∅ := by
  simp [pendingPatch, empty, FMap.keys]

/-- Without pending sandboxes, the overlay relation gives final filesystem agreement. -/
theorem empty_filesystems {witnesses : WitnessMap sig}
    {incr : Prefix m h .incr prog start} {vanilla : Prefix m h .vanilla prog start}
    (related : BisimRelated witnesses incr vanilla) (empty : incr.final.sandbox = ∅) :
    FSApprox incr.final.fs vanilla.final.fs := by
  have overlay := related.overlay
  rw [pending_empty empty, Incr.applyPatch_empty] at overlay
  exact FSApprox.of_contents (fun q => (overlay.contents q).symm)

/-- H5 transfers completion, and completion removes the pending overlay. -/
theorem completion (host : HostWellFormed m h) {witnesses : WitnessMap sig}
    (incr : Prefix m h .incr prog start) (vanilla : Prefix m h .vanilla prog start)
    (related : BisimRelated witnesses incr vanilla) :
    (h.complete prog incr.final ↔ h.complete prog vanilla.final) ∧
      (h.complete prog incr.final → terminal incr.trace = terminal vanilla.trace ∧
        incr.final.ec = vanilla.final.ec ∧ FSApprox incr.final.fs vanilla.final.fs) := by
  have control := final_control related
  have transfer (ib : incr.final.buffer = ∅) (is : incr.final.sandbox = ∅)
      (vb : vanilla.final.buffer = ∅) (vs : vanilla.final.sandbox = ∅) :
      h.complete prog incr.final ↔ h.complete prog vanilla.final :=
    host.completionInvariance prog _ _ ib is vb vs control.1 control.2.1
      control.2.2.1 control.2.2.2.2 (empty_filesystems related is)
  constructor
  · constructor
    · intro completed
      obtain ⟨ib, is⟩ := host.completionEmpty prog _ completed
      have vb : vanilla.final.buffer = ∅ := control.2.2.2.1.symm.trans ib
      have vs : vanilla.final.sandbox = ∅ := FMap.eq_empty_of_dom_eq_empty _ (by
        rw [← related.sandboxDomains, is, FMap.dom_empty])
      exact (transfer ib is vb vs).mp completed
    · intro completed
      obtain ⟨vb, vs⟩ := host.completionEmpty prog _ completed
      have ib : incr.final.buffer = ∅ := control.2.2.2.1.trans vb
      have is : incr.final.sandbox = ∅ := FMap.eq_empty_of_dom_eq_empty _ (by
        rw [related.sandboxDomains, vs, FMap.dom_empty])
      exact (transfer ib is vb vs).mpr completed
  · intro completed
    exact ⟨related.terminal, control.2.1,
      empty_filesystems related (host.completionEmpty prog _ completed).2⟩

/-- Initial records give admissibility of either zero-step prefix. -/
theorem empty_admissible (executor : Executor) (initial : Initial h prog start)
    (witnesses : WitnessMap sig)
    (records : TimestampConsistent (worldPaperRecords start ∪ witnessPaperRecords witnesses)) :
    Admissible witnesses (emptyPrefix m h executor prog start initial) := by
  have timestamps : TimestampConsistent (worldPaperRecords start) :=
    records.mono (fun _ member => Or.inl member)
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro d member
    cases member
  · simpa [Prefix.paperRecords, emptyPrefix] using timestamps
  · intro entry i j distinct
    simp [componentWrites, componentAccesses, componentDeps, componentSteps, emptyPrefix]
  · simpa [Prefix.paperRecords, emptyPrefix] using records

/-- The exact `def:paper-bisim-relation` relation contains the two initial prefixes. -/
theorem initial (initial : Initial h prog start) (shape : DenotationShape m)
    (commands : WellFormedCommands m) (key : HashInjective m) (host : HostWellFormed m h)
    (cache : WellFormedCache m start.cache) (witnesses : WitnessMap sig)
    (records : TimestampConsistent (worldPaperRecords start ∪ witnessPaperRecords witnesses)) :
    BisimRelated witnesses (emptyPrefix m h .incr prog start initial)
      (emptyPrefix m h .vanilla prog start initial) := by
  let incr := emptyPrefix m h .incr prog start initial
  let vanilla := emptyPrefix m h .vanilla prog start initial
  have ai := empty_admissible (m := m) .incr initial witnesses records
  have av := empty_admissible (m := m) .vanilla initial witnesses records
  refine {
    incrAdmissible := ai
    vanillaAdmissible := av
    equalLength := rfl
    steps := .nil
    cache := cache
    vanillaCache := rfl
    sandboxDomains := rfl
    vanillaEmpty := av.operational.vanilla_initial_fields host
    incrSandboxes := (buffer_sandbox_preservation shape commands key host incr ai.operational).1
    incrPrefixes := (cacheable_prefixes shape commands key host cache incr ai.operational).2.1
    disjointPatches := ?_
    overlay := ?_
    paths := ?_ }
  · intro i j sb sb' distinct hs
    simp [emptyPrefix, initial.2.1, FMap.get] at hs
  · change FSApprox start.fs (applyPatch start.fs (pendingPatch start))
    rw [pending_empty initial.2.1, Incr.applyPatch_empty]
    exact FSApprox.of_contents (fun _ => rfl)
  · intro k
    constructor <;> ext q <;>
      simp [componentWrites, componentAccesses, componentDeps, componentSteps, emptyPrefix]

end
end Incr.Incr.BisimulationBasis


