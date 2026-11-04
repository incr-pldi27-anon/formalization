import Incr.IncrPP.Preservation.HistoryAlgebra

/-!
# Live accumulation along actual retained component histories

A surviving entry either receives its own open result or retains its old
payload across a foreign step. Closing judgments erase their own entry.
-/

namespace Incr.IncrPP

noncomputable section

/-- An erased key has no surviving lookup. -/
theorem lookup_erase_ne {K V : Type} [DecidableEq K] {map : FMap K V} {removed key : K} {value : V}
    (lookup : FMap.get (map ∖ removed) key = some value) : key ≠ removed := by
  intro equal
  subst key
  simp only [FMap.get_erase_self] at lookup
  contradiction

variable {sig : Signature} {m : CommandModel sig} {h : Host sig} {prog : sig.Prog} {start : World sig}

/-- A surviving payload is either its own open accumulation or an unchanged foreign payload. -/
theorem LiveDerivation.history_effect {before after : World sig} {head : Head sig}
    {returned : Option Chunk} (d : LiveDerivation m before head after returned)
    {slot : Nat} {sb : Sandbox sig} (present : FMap.get after.sandbox slot = some sb) :
    (∃ p, head = .pipeline p slot ∧ (LiveDerivation.input d).flag = .open ∧
      ∃ old : Sandbox sig, ∃ (hin : old.input.flag = .open) (hout : old.output.flag = .open),
        FMap.get before.sandbox slot = some old ∧
          sb = old.accumulate (LiveDerivation.input d) (LiveDerivation.result d) hin hout) ∨
    (FMap.get before.sandbox slot = some sb ∧ ∀ p, head ≠ .pipeline p slot) := by
  cases d
  case pipelineOpen =>
    rcases lookup_set_origin present with ⟨rfl, rfl⟩ | ⟨different, prior⟩
    · refine Or.inl ⟨_, rfl, rfl, ‹Sandbox sig›, ?_, ?_, ?_, ?_⟩
      all_goals first | assumption | rfl
    · refine Or.inr ⟨prior, ?_⟩
      intro p same
      exact different (Head.pipeline.inj same).2.symm
  all_goals first
    | exact Or.inr ⟨present, fun p same => nomatch same⟩
    | exact Or.inr ⟨lookup_erase_origin present,
        fun p same => lookup_erase_ne present (Head.pipeline.inj same).2.symm⟩

/-- Accumulated fields match the actual history of each currently live component. -/
def LiveHistories (pre : Prefix m h .live prog start) (b : Boundary pre) : Prop :=
  ∀ entry slot sb, b.livePipeline entry slot → FMap.get b.world.sandbox slot = some sb →
    HistoryFields (componentSteps pre.trace (.pipeline entry slot)) sb

/-- Selection retains histories, or creates an initial payload with an empty fresh history. -/
theorem LiveHistories.selected (pre : Prefix m h .live prog start)
    (histories : LiveHistories pre .final) (selection : Selection sig) (world : World sig)
    (allowed : h.select prog pre.final selection world)
    (discipline : SelectionDiscipline pre.trace pre.final selection world) :
    LiveHistories pre (.selected selection world allowed) := by
  intro entry slot sb live present
  rcases discipline with ⟨_, _, _, allocation, _⟩
  cases initializes : selection.init with
  | none =>
    simp only [initializes] at allocation
    have oldLive : (Boundary.final : Boundary pre).livePipeline entry slot := by
      simpa [Boundary.livePipeline, Boundary.currentEntry, Boundary.componentDomain,
        Boundary.selection?, initializes] using live
    have old : FMap.get pre.final.sandbox slot = some sb := by
      simpa only [Boundary.world, allocation.1] using present
    exact histories entry slot sb oldLive old
  | some init =>
    simp only [initializes] at allocation
    have index : pre.trace.length = entry := by
      simpa [Boundary.currentEntry, Boundary.selection?, initializes] using live.1
    subst entry
    have initial : sb = Sandbox.initial pre.final.fs := by
      apply initialSandboxes_value init pre.final.fs
      simpa only [Boundary.world, allocation.2.2.2.2] using present
    subst sb
    rw [componentSteps_fresh pre.trace pre.trace.length slot (Nat.le_refl _)]
    exact HistoryFields.initial _

/-- Each surviving entry appends its own open result, or keeps its history across a foreign step. -/
theorem LiveHistories.after_step (pre post : Prefix m h .live prog start)
    (d : StepDerivation m h .live prog) (allowed : h.select prog pre.final d.selection d.selected)
    (joined : post.trace = pre.trace ++ [d]) (after : post.final = d.after)
    (histories : LiveHistories pre (.selected d.selection d.selected allowed)) : LiveHistories post .final := by
  intro entry slot sb live present
  have oldLive := ((Boundary.livePipeline_after_step pre post d allowed joined entry slot).mp live).1
  have actual : FMap.get d.after.sandbox slot = some sb := by
    simpa only [Boundary.world, after] using present
  rcases LiveDerivation.history_effect d.probe actual with own | foreign
  · obtain ⟨p, head, _, old, hin, hout, prior, rfl⟩ := own
    have fields := histories entry slot old oldLive prior
    have selected : componentAt (pre.trace ++ [d]) pre.trace.length d = some (.pipeline entry slot) := by
      rw [Boundary.componentAt_selected pre d allowed head, oldLive.1]
      rfl
    simp only [joined, componentSteps_snoc, selected, ite_true]
    exact HistoryFields.accumulate _ d old fields hin hout
  · obtain ⟨prior, foreignHead⟩ := foreign
    have notSelected : componentAt (pre.trace ++ [d]) pre.trace.length d ≠ some (.pipeline entry slot) := by
      intro selected
      obtain ⟨p, head⟩ := componentAt_pipeline_head _ _ _ selected
      exact foreignHead p head
    simp only [joined, componentSteps_snoc, notSelected, ite_false, List.append_nil]
    exact histories entry slot sb oldLive prior

/-- Operational live endpoints satisfy the accumulated history equations. -/
theorem Operational.liveHistories_final (host : HostWellFormed m h)
    (pre : Prefix m h .live prog start) (operational : Operational pre) : LiveHistories pre .final := by
  apply Operational.snoc_induction (fun pre => LiveHistories pre .final) ?_ ?_ pre operational
  · intro pre _ empty entry slot sb _ present
    have connected := pre.connected
    rw [empty] at connected
    have endpoint := (Connected.nil_iff start pre.final).mp connected
    simp [Boundary.world, endpoint, pre.initial.2.1, FMap.get] at present
  · intro short post d shortOperational _ joined before after ih
    have allowed : h.select prog short.final d.selection d.selected := by
      simpa only [before] using d.host
    have discipline := host.selectionDiscipline .live prog start short shortOperational
      d.selection d.selected allowed
    exact LiveHistories.after_step short post d allowed joined after
      (LiveHistories.selected short ih d.selection d.selected allowed discipline)

/-- The live history equations hold after every permitted selection, with no future-step premise. -/
theorem Operational.liveHistories (host : HostWellFormed m h)
    (pre : Prefix m h .live prog start) (operational : Operational pre) (b : Boundary pre) :
    LiveHistories pre b := by
  have endpoint := Operational.liveHistories_final host pre operational
  cases b with
  | final => exact endpoint
  | selected selection world allowed =>
    exact LiveHistories.selected pre endpoint selection world allowed
      (host.selectionDiscipline .live prog start pre operational selection world allowed)

end
end IncrPP
end Incr
