import Incr.IncrPP.Preservation.OrderPrefixes

/-!
# Retained step intervals

A component cannot take another step after it closes. The proof uses the
actual connected prefix before that step and the host slot discipline.
-/

namespace Incr.IncrPP

noncomputable section

variable {sig : Signature} {m : CommandModel sig} {h : Host sig}
  {executor : Executor} {prog : sig.Prog} {start : World sig}

/-- A recorded step supplies the exact connected prefix ending at its before-world. -/
theorem Connected.before_at {trace : Trace m h executor prog} {final : World sig}
    (connected : Connected start trace final) {pos : Nat} {d : StepDerivation m h executor prog}
    (atPos : (trace)[pos]? = some d) : Connected start (trace.take pos) d.before := by
  induction connected generalizing pos with
  | nil => simp at atPos
  | cons step rest final tail ih =>
    cases pos with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at atPos
      subst d
      exact Connected.nil _
    | succ pos =>
      simp only [List.getElem?_cons_succ] at atPos
      simpa only [List.take_succ_cons] using Connected.cons step (rest.take pos) d.before (ih atPos)

/-- Before any actual component step, that component has not already closed. -/
theorem Operational.no_close_before_step (host : HostWellFormed m h)
    (pre : Prefix m h executor prog start) (operational : Operational pre)
    (pos : Nat) (d : StepDerivation m h executor prog) (k : Component)
    (atPos : (pre.trace)[pos]? = some d) (component : componentAt pre.trace pos d = some k) :
    closingPositions (pre.trace.take pos) k = [] := by
  have bound := (List.getElem?_eq_some_iff.mp atPos).choose
  let short : Prefix m h executor prog start :=
    ⟨pre.trace.take pos, d.before, pre.initial, pre.connected.before_at atPos⟩
  have shorter : short.trace.IsPrefix pre.trace := List.take_prefix _ _
  have shortOperational := operational.of_trace_isPrefix shorter
  have allowed : h.select prog short.final d.selection d.selected := d.host
  have allocation := Operational.slotAllocation host short shortOperational
    (.selected d.selection d.selected allowed)
  have shortLength : short.trace.length = pos := by
    simp [short, List.length_take, Nat.min_eq_left (Nat.le_of_lt bound)]
  have taken : pre.trace.take (pos + 1) = short.trace ++ [d] := by
    simp [short, List.take_add_one, atPos]
  have pref : (short.trace ++ [d]).IsPrefix pre.trace := by
    rw [← taken]
    exact List.take_prefix _ _
  obtain ⟨extra, joined⟩ := pref
  have selected : componentAt (short.trace ++ [d]) short.trace.length d = some k := by
    rw [shortLength]
    have extension : componentAt pre.trace pos d = componentAt (short.trace ++ [d]) pos d := by
      rw [← joined]
      apply componentAt_append
      simp [shortLength]
    rw [← extension]
    exact component
  exact StepDerivation.no_prior_close short d allowed allocation k selected

/-- An actual component step is no later than that component's last position. -/
theorem Operational.step_le_lastPosition (host : HostWellFormed m h)
    (pre : Prefix m h executor prog start) (operational : Operational pre)
    (pos : Nat) (d : StepDerivation m h executor prog) (k : Component)
    (atPos : (pre.trace)[pos]? = some d) (component : componentAt pre.trace pos d = some k) :
    paperPosition pos ≤ lastPosition pre.trace k := by
  have bound := (List.getElem?_eq_some_iff.mp atPos).choose
  have noPrior := Operational.no_close_before_step host pre operational pos d k atPos component
  cases closing : closingPositions pre.trace k with
  | nil => simpa [lastPosition, closing, paperPosition] using Nat.succ_le_of_lt bound
  | cons first rest =>
    have member : first ∈ closingPositions pre.trace k := by simp [closing]
    have notEarlier : paperPosition pos ≤ first := by
      by_contra earlier
      have firstOld : first ≤ (pre.trace.take pos).length := by
        simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt bound)]
        exact Nat.le_of_lt_succ (Nat.lt_of_not_ge earlier)
      have oldMember : first ∈ closingPositions (pre.trace.take pos) k := by
        apply closingPositions_append_old (pre.trace.take pos) (pre.trace.drop pos) k first
        · simpa only [List.take_append_drop] using member
        · exact firstOld
      simp [noPrior] at oldMember
    simpa [lastPosition, closing] using notEarlier

/-- An ordered foreign slot cannot write a path during another slot's protected interval. -/
theorem Operational.ordered_pipeline_no_foreign_write (host : HostWellFormed m h)
    (pre : Prefix m h executor prog start) (operational : Operational pre) (ordered : ExitOrdered pre.trace)
    (entry writer target : Nat) (different : writer ≠ target)
    (writerDomain : .pipeline entry writer ∈ componentDomain pre.trace)
    (protectedDomain : .pipeline entry target ∈ componentDomain pre.trace)
    (q : sig.Path) (accessed : q ∈ componentAccesses pre.trace (.pipeline entry target))
    (pos : Nat) (d : StepDerivation m h executor prog)
    (atPos : (pre.trace)[pos]? = some d)
    (writerAt : componentAt pre.trace pos d = some (.pipeline entry writer))
    (afterFirst : firstAccess pre.trace (.pipeline entry target) q accessed ≤ paperPosition pos)
    (beforeLast : paperPosition pos ≤ lastPosition pre.trace (.pipeline entry target)) :
    q ∉ FMap.dom (ProbeDerivation.result d.probe).patch := by
  intro written
  have writerStep : d ∈ componentSteps pre.trace (.pipeline entry writer) :=
    (mem_componentSteps_iff pre.trace _ d).mpr ⟨pos, atPos, writerAt⟩
  have writerWrites : q ∈ componentWrites pre.trace (.pipeline entry writer) := ⟨d, writerStep, written⟩
  have writerAccess : q ∈ componentAccesses pre.trace (.pipeline entry writer) := Or.inr writerWrites
  have posAccess : paperPosition pos ∈ accessPositions pre.trace (.pipeline entry writer) q :=
    (mem_accessPositions_iff pre.trace _ q _).mpr ⟨pos, d, atPos, writerAt, Or.inl (Or.inl written), rfl⟩
  have writerFirst := (firstAccess_spec pre.trace _ q writerAccess).2.2.2 _ posAccess
  have writerLast := Operational.step_le_lastPosition host pre operational pos d _ atPos writerAt
  have order := ordered entry writer target writerDomain protectedDomain different q ⟨writerWrites, accessed⟩
  rcases order with earlier | later
  · exact Nat.not_lt_of_ge (Nat.le_trans afterFirst writerLast) earlier
  · exact Nat.not_lt_of_ge (Nat.le_trans writerFirst beforeLast) later

/-- The actual filesystem is unchanged across an ordered foreign slot's step. -/
theorem Operational.ordered_pipeline_foreign_frame (host : HostWellFormed m h)
    (pre : Prefix m h executor prog start) (operational : Operational pre) (ordered : ExitOrdered pre.trace)
    (entry writer target : Nat) (different : writer ≠ target)
    (writerDomain : .pipeline entry writer ∈ componentDomain pre.trace)
    (targetDomain : .pipeline entry target ∈ componentDomain pre.trace)
    (q : sig.Path) (accessed : q ∈ componentAccesses pre.trace (.pipeline entry target))
    (pos : Nat) (d : StepDerivation m h executor prog) (atPos : (pre.trace)[pos]? = some d)
    (writerAt : componentAt pre.trace pos d = some (.pipeline entry writer))
    (afterFirst : firstAccess pre.trace (.pipeline entry target) q accessed ≤ paperPosition pos)
    (beforeLast : paperPosition pos ≤ lastPosition pre.trace (.pipeline entry target)) :
    FMap.get d.after.fs q = FMap.get d.selected.fs q := by
  exact ProbeDerivation.fs_frame d.probe q
    (Operational.ordered_pipeline_no_foreign_write host pre operational ordered entry writer target
      different writerDomain targetDomain q accessed pos d atPos writerAt afterFirst beforeLast)

/-- The unique actual close is the paper's last position. -/
theorem Operational.lastPosition_eq_closing (host : HostWellFormed m h)
    (pre : Prefix m h executor prog start) (operational : Operational pre) (k : Component)
    (position : Nat) (member : position ∈ closingPositions pre.trace k) :
    lastPosition pre.trace k = position := by
  have unique := Operational.closing_unique host pre operational k
  cases closing : closingPositions pre.trace k with
  | nil => simp [closing] at member
  | cons first rest =>
    cases rest with
    | nil =>
      have eq : position = first := by simpa [closing] using member
      simpa [lastPosition, closing] using eq.symm
    | cons second tail => simp [closing] at unique

/-- A protected position cannot follow a close of its target component. -/
theorem Operational.no_close_before_interval (host : HostWellFormed m h)
    (pre : Prefix m h executor prog start) (operational : Operational pre) (k : Component)
    (pos : Nat) (bound : pos < pre.trace.length)
    (within : paperPosition pos ≤ lastPosition pre.trace k) :
    closingPositions (pre.trace.take pos) k = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro first member
  have inLong : first ∈ closingPositions pre.trace k := by
    have lifted := closingPositions_append_member (pre.trace.take pos) (pre.trace.drop pos) k first member
    simpa only [List.take_append_drop] using lifted
  have firstEq := Operational.lastPosition_eq_closing host pre operational k first inLong
  have earlier := (closingPositions_bounds (pre.trace.take pos) k first member).2
  simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt bound)] at earlier
  rw [firstEq] at within
  exact Nat.not_lt_of_ge earlier within

/-- Once a pipeline component has accessed a path, its initialization is not later. -/
theorem firstAccess_pipeline_entry_le (trace : Trace m h executor prog) (entry slot : Nat)
    (q : sig.Path) (accessed : q ∈ componentAccesses trace (.pipeline entry slot))
    (pos : Nat) (afterFirst : firstAccess trace (.pipeline entry slot) q accessed ≤ paperPosition pos) :
    entry ≤ pos := by
  have first := (firstAccess_spec trace _ q accessed).1
  obtain ⟨firstPos, firstStep, _, component, _, firstEq⟩ :=
    (mem_accessPositions_iff trace _ q _).mp first
  have initialized := componentAt_pipeline_entry_le trace firstPos firstStep component
  rw [firstEq] at afterFirst
  exact Nat.le_trans initialized (Nat.le_of_succ_le_succ afterFirst)

/-- A recorded initialization and all its slots remain in a prefix containing that position. -/
theorem pipeline_domain_take (trace : Trace m h executor prog) (entry slot n : Nat)
    (member : .pipeline entry slot ∈ componentDomain trace) (inside : entry < n) :
    .pipeline entry slot ∈ componentDomain (trace.take n) := by
  obtain ⟨pos, d, atPos, kind⟩ := member
  rcases kind with ⟨p, head, impossible⟩ | ⟨init, i, initializes, bound, equal⟩
  · cases impossible
  · cases equal
    refine ⟨entry, d, ?_, Or.inr ⟨init, slot, initializes, bound, rfl⟩⟩
    simp only [List.getElem?_take, inside, ite_true]
    exact atPos

/-- A protected pipeline interval selects the same live epoch at every recorded position. -/
theorem Operational.interval_pipeline_selection (host : HostWellFormed m h)
    (pre : Prefix m h executor prog start) (operational : Operational pre)
    (entry slot : Nat) (domain : .pipeline entry slot ∈ componentDomain pre.trace)
    (q : sig.Path) (accessed : q ∈ componentAccesses pre.trace (.pipeline entry slot))
    (pos : Nat) (d : StepDerivation m h executor prog) (atPos : (pre.trace)[pos]? = some d)
    (afterFirst : firstAccess pre.trace (.pipeline entry slot) q accessed ≤ paperPosition pos)
    (beforeLast : paperPosition pos ≤ lastPosition pre.trace (.pipeline entry slot)) :
    ∃ p writer, d.selection.head = .pipeline p writer ∧
      componentAt pre.trace pos d = some (.pipeline entry writer) ∧
      .pipeline entry writer ∈ componentDomain pre.trace := by
  have bound := (List.getElem?_eq_some_iff.mp atPos).choose
  let short : Prefix m h executor prog start :=
    ⟨pre.trace.take pos, d.before, pre.initial, pre.connected.before_at atPos⟩
  have shorter : short.trace.IsPrefix pre.trace := List.take_prefix pos pre.trace
  have shortOperational := operational.of_trace_isPrefix shorter
  have allowed : h.select prog short.final d.selection d.selected := d.host
  have allocation := Operational.slotAllocation host short shortOperational
    (.selected d.selection d.selected allowed)
  have shortLength : short.trace.length = pos := by
    simp [short, List.length_take, Nat.min_eq_left (Nat.le_of_lt bound)]
  have taken : pre.trace.take (pos + 1) = short.trace ++ [d] := by
    simp [short, List.take_add_one, atPos]
  have pref : (short.trace ++ [d]).IsPrefix pre.trace := by
    rw [← taken]
    exact List.take_prefix _ _
  obtain ⟨extra, joined⟩ := pref
  have entryLe := firstAccess_pipeline_entry_le pre.trace entry slot q accessed pos afterFirst
  have targetIn : .pipeline entry slot ∈ (Boundary.selected d.selection d.selected allowed).componentDomain := by
    apply (Boundary.pipelineDomain_snoc short d allowed entry slot).mp
    rw [← taken]
    exact pipeline_domain_take pre.trace entry slot (pos + 1) domain (Nat.lt_succ_of_le entryLe)
  have noClose : closingPositions short.trace (.pipeline entry slot) = [] :=
    Operational.no_close_before_interval host pre operational _ pos bound beforeLast
  have current : (Boundary.selected d.selection d.selected allowed).currentEntry = some entry := by
    by_contra different
    exact allocation.retired entry slot targetIn different noClose
  have allocated : slot ∈ FMap.dom d.selected.buffer := by
    change slot ∈ FMap.dom (Boundary.selected d.selection d.selected allowed).world.buffer
    rw [allocation.buffers]
    exact ⟨entry, current, targetIn, noClose⟩
  have discipline := host.selectionDiscipline executor prog start short shortOperational
    d.selection d.selected allowed
  cases head : d.selection.head with
  | standalone p =>
    have branch := discipline.2.2.2.2
    rw [head] at branch
    have empty : d.selected.buffer = ∅ := branch.2.2.2.1
    simp [empty] at allocated
  | pipeline p writer =>
    have named : componentAt (short.trace ++ [d]) short.trace.length d = some (.pipeline entry writer) := by
      rw [Boundary.componentAt_selected short d allowed head, current]
      rfl
    have longNamed : componentAt pre.trace pos d = some (.pipeline entry writer) := by
      rw [← joined, componentAt_append _ _ pos d (by simp [shortLength]), ← shortLength]
      exact named
    have present := ProbeDerivation.pipeline_buffer_present (head ▸ d.probe)
    change writer ∈ FMap.dom (Boundary.selected d.selection d.selected allowed).world.buffer at present
    rw [allocation.buffers] at present
    obtain ⟨actualEntry, actualCurrent, actualDomain, _⟩ := present
    rw [current] at actualCurrent
    have same : actualEntry = entry := Option.some.inj actualCurrent.symm
    subst actualEntry
    have historical : .pipeline entry writer ∈ componentDomain (short.trace ++ [d]) :=
      (Boundary.pipelineDomain_snoc short d allowed entry writer).mpr actualDomain
    refine ⟨p, writer, rfl, longNamed, ?_⟩
    rw [← joined]
    exact componentDomain_append_subset _ extra historical

/-- Every standalone rule consumes EOF input. -/
theorem ProbeDerivation.standalone_input_eof {before after : World sig} {p : sig.Probe}
    {returned : Option Chunk} (d : ProbeDerivation m executor before (.standalone p) after returned) :
    (ProbeDerivation.input d).flag = .eof := by
  cases executor <;> cases d <;> rfl

/-- A retained standalone head keeps the same input flag witness. -/
theorem ProbeDerivation.input_eof_of_standalone {before after : World sig} {head : Head sig}
    {returned : Option Chunk} (d : ProbeDerivation m executor before head after returned)
    {p : sig.Probe} (standalone : head = .standalone p) :
    (ProbeDerivation.input d).flag = .eof := by
  subst head
  exact d.standalone_input_eof

/-- A standalone component has exactly its invocation position as last position. -/
theorem Operational.standalone_lastPosition (host : HostWellFormed m h)
    (pre : Prefix m h executor prog start) (operational : Operational pre) (entry : Nat)
    (domain : .standalone entry ∈ componentDomain pre.trace) :
    lastPosition pre.trace (.standalone entry) = paperPosition entry := by
  obtain ⟨pos, d, atPos, kind⟩ := domain
  rcases kind with ⟨p, head, equal⟩ | ⟨init, slot, initializes, bound, impossible⟩
  · cases equal
    have component : componentAt pre.trace entry d = some (.standalone entry) := by
      simp [componentAt, head]
    have eof : (ProbeDerivation.input d.probe).flag = .eof := d.probe.input_eof_of_standalone head
    have close : paperPosition entry ∈ closingPositions pre.trace (.standalone entry) :=
      (mem_closingPositions_iff pre.trace _ _).mpr ⟨entry, d, atPos, component, eof, rfl⟩
    exact Operational.lastPosition_eq_closing host pre operational _ _ close
  · cases impossible

/-- The first access of a standalone component is its only invocation position. -/
theorem firstAccess_standalone (trace : Trace m h executor prog) (entry : Nat) (q : sig.Path)
    (accessed : q ∈ componentAccesses trace (.standalone entry)) :
    firstAccess trace (.standalone entry) q accessed = paperPosition entry := by
  have first := (firstAccess_spec trace _ q accessed).1
  obtain ⟨pos, d, _, component, _, eq⟩ := (mem_accessPositions_iff trace _ q _).mp first
  have same := componentAt_standalone_index trace pos d component
  simpa [same] using eq

/-- E.5's inclusive protected interval excludes every foreign filesystem change. -/
theorem Operational.noForeignChanges (host : HostWellFormed m h)
    (pre : Prefix m h executor prog start) (operational : Operational pre) (ordered : ExitOrdered pre.trace) :
    ∀ k ∈ componentDomain pre.trace, ∀ q (accessed : q ∈ componentAccesses pre.trace k),
      ∀ pos d, (pre.trace)[pos]? = some d → componentAt pre.trace pos d ≠ some k →
        firstAccess pre.trace k q accessed ≤ paperPosition pos → paperPosition pos ≤ lastPosition pre.trace k →
          FMap.get d.after.fs q = FMap.get d.selected.fs q := by
  intro k domain q accessed pos d atPos foreign afterFirst beforeLast
  cases k with
  | standalone entry =>
    have firstEq := firstAccess_standalone pre.trace entry q accessed
    have lastEq := Operational.standalone_lastPosition host pre operational entry domain
    rw [firstEq] at afterFirst
    rw [lastEq] at beforeLast
    have posEq : pos = entry := by
      have eq : paperPosition pos = paperPosition entry := Nat.le_antisymm beforeLast afterFirst
      exact Nat.succ.inj eq
    subst pos
    have first := (firstAccess_spec pre.trace (.standalone entry) q accessed).1
    obtain ⟨firstPos, firstStep, firstAt, firstComponent, _, firstPosition⟩ :=
      (mem_accessPositions_iff pre.trace _ q _).mp first
    rw [firstEq] at firstPosition
    have firstPosEq : entry = firstPos := Nat.succ.inj firstPosition
    subst firstPos
    rw [atPos] at firstAt
    cases Option.some.inj firstAt
    exact False.elim (foreign firstComponent)
  | pipeline entry slot =>
    obtain ⟨p, writer, head, named, writerDomain⟩ :=
      Operational.interval_pipeline_selection host pre operational entry slot domain q accessed
        pos d atPos afterFirst beforeLast
    have different : writer ≠ slot := by
      intro equal
      subst writer
      exact foreign named
    exact Operational.ordered_pipeline_foreign_frame host pre operational ordered
      entry writer slot different writerDomain domain q accessed pos d atPos named afterFirst beforeLast

end
end IncrPP
end Incr
