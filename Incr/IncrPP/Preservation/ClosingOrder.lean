import Incr.IncrPP.Preservation.Allocation

/-!
# Ordered pipeline closings for E.4

An EOF buffer has no lower allocated buffer. Exact allocation then gives
an earlier closing witness for every lower initialized slot. Historical
closing positions persist when later steps are recorded.
-/

namespace Incr.IncrPP

variable {sig : Signature} {m : CommandModel sig} {h : Host sig}
  {executor : Executor} {prog : sig.Prog} {start : World sig}

/-- An actual pipeline closing has an initialization strictly before the prefix end. -/
theorem closingPosition_entry_lt (trace : Trace m h executor prog) {entry slot position : Nat}
    (member : position ∈ closingPositions trace (.pipeline entry slot)) : entry < trace.length := by
  obtain ⟨pos, d, atPos, component, _, _⟩ := (mem_closingPositions_iff trace _ position).mp member
  exact Nat.lt_of_le_of_lt (componentAt_pipeline_entry_le trace pos d component)
    (List.getElem?_eq_some_iff.mp atPos).choose

/-- A selected component with an older entry is already in the recorded domain. -/
theorem Boundary.pipelineDomain_old (pre : Prefix m h executor prog start)
    (selection : Selection sig) (world : World sig) (allowed : h.select prog pre.final selection world)
    {entry slot : Nat} (bound : entry < pre.trace.length)
    (present : .pipeline entry slot ∈ (Boundary.selected selection world allowed).componentDomain) :
    .pipeline entry slot ∈ Incr.IncrPP.componentDomain pre.trace := by
  rcases present with old | ⟨init, i, _, _, equal⟩
  · exact old
  · have index : entry = pre.trace.length := (Component.pipeline.inj equal).1
    exact False.elim (Nat.lt_irrefl _ (index ▸ bound))

/-- Every higher-slot closing follows an actual lower-slot closing in the same pipeline. -/
theorem Operational.closing_order (host : HostWellFormed m h)
    (pre : Prefix m h executor prog start) (operational : Operational pre) :
    ∀ entry i j, .pipeline entry i ∈ componentDomain pre.trace →
      .pipeline entry j ∈ componentDomain pre.trace → i < j →
      ∀ position ∈ closingPositions pre.trace (.pipeline entry j),
        ∃ earlier ∈ closingPositions pre.trace (.pipeline entry i), earlier < position := by
  classical
  apply Operational.snoc_induction
    (fun pre => ∀ entry i j, .pipeline entry i ∈ componentDomain pre.trace →
      .pipeline entry j ∈ componentDomain pre.trace → i < j →
      ∀ position ∈ closingPositions pre.trace (.pipeline entry j),
        ∃ earlier ∈ closingPositions pre.trace (.pipeline entry i), earlier < position) ?_ ?_ pre operational
  · intro pre _ empty entry i j present
    simp [empty, componentDomain] at present
  · intro short post d shortOperational _ joined before after ih entry i j domainI domainJ less position closed
    have allowed : h.select prog short.final d.selection d.selected := by
      simpa only [before] using d.host
    rw [joined] at domainI domainJ
    have selectedI := (Boundary.pipelineDomain_snoc short d allowed entry i).mp domainI
    have selectedJ := (Boundary.pipelineDomain_snoc short d allowed entry j).mp domainJ
    rw [joined, closingPositions_snoc] at closed
    rcases List.mem_append.mp closed with old | newest
    · have bound := closingPosition_entry_lt short.trace old
      have oldI := Boundary.pipelineDomain_old short d.selection d.selected allowed bound selectedI
      have oldJ := Boundary.pipelineDomain_old short d.selection d.selected allowed bound selectedJ
      obtain ⟨earlier, member, earlierBefore⟩ := ih entry i j oldI oldJ less position old
      refine ⟨earlier, ?_, earlierBefore⟩
      rw [joined, closingPositions_snoc]
      exact List.mem_append_left _ member
    · split at newest
      next closes =>
        simp only [List.mem_singleton] at newest
        subst position
        cases head : d.selection.head with
        | standalone p => simp [componentAt_snoc, head] at closes
        | pipeline p slot =>
          have allocation := Operational.slotAllocation host short shortOperational
            (.selected d.selection d.selected allowed)
          have buffersEq : FMap.dom d.selected.buffer =
              (Boundary.selected d.selection d.selected allowed).unclosedSlots := allocation.buffers
          obtain ⟨chunk, lookup, flag⟩ := d.probe.pipeline_buffer_flag head
          have present : slot ∈ FMap.dom d.selected.buffer := Finmap.mem_of_lookup_eq_some lookup
          rw [buffersEq] at present
          obtain ⟨owner, current, _, _⟩ := present
          have named : componentAt (short.trace ++ [d]) short.trace.length d = some (.pipeline owner slot) := by
            rw [Boundary.componentAt_selected short d allowed head, current]
            rfl
          have indices : owner = entry ∧ slot = j :=
            Component.pipeline.inj (Option.some.inj (named.symm.trans closes.1))
          obtain ⟨rfl, rfl⟩ := indices
          have oldClosed : closingPositions short.trace (.pipeline owner i) ≠ [] := by
            intro unclosed
            have allocated : i ∈ FMap.dom d.selected.buffer := by
              rw [buffersEq]
              exact ⟨owner, current, selectedI, unclosed⟩
            obtain ⟨lower, lowerLookup⟩ := Finmap.mem_iff.mp allocated
            have order := Boundary.bufferOrder host short shortOperational
              (.selected d.selection d.selected allowed)
            have openFlag := order i slot lower chunk less lowerLookup lookup
            cases (flag.trans closes.2).symm.trans openFlag
          obtain ⟨earlier, member⟩ := List.exists_mem_of_ne_nil _ oldClosed
          refine ⟨earlier, ?_, ?_⟩
          · rw [joined, closingPositions_snoc]
            exact List.mem_append_left _ member
          · exact Nat.lt_of_le_of_lt (closingPositions_bounds short.trace _ earlier member).2
              (Nat.lt_succ_self _)
      next => simp at newest

/-- E.4's closing-order clause also covers pending selected initializations. -/
theorem Boundary.closing_order (host : HostWellFormed m h)
    (pre : Prefix m h executor prog start) (operational : Operational pre) (b : Boundary pre) :
    ∀ entry i j, .pipeline entry i ∈ b.componentDomain → .pipeline entry j ∈ b.componentDomain → i < j →
      ∀ position ∈ closingPositions pre.trace (.pipeline entry j),
        ∃ earlier ∈ closingPositions pre.trace (.pipeline entry i), earlier < position := by
  intro entry i j domainI domainJ less position closed
  have bound := closingPosition_entry_lt pre.trace closed
  cases b with
  | final =>
    apply Operational.closing_order host pre operational entry i j
    · simpa [Boundary.componentDomain, Boundary.selection?] using domainI
    · simpa [Boundary.componentDomain, Boundary.selection?] using domainJ
    · exact less
    · exact closed
  | selected selection world allowed =>
    exact Operational.closing_order host pre operational entry i j
      (Boundary.pipelineDomain_old pre selection world allowed bound domainI)
      (Boundary.pipelineDomain_old pre selection world allowed bound domainJ) less position closed

end IncrPP
end Incr
