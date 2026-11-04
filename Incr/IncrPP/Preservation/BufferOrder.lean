import Incr.IncrPP.WellFormedness.Host
import Incr.IncrPP.WellFormedness.Boundary
import Incr.IncrPP.Preservation.Prefixes

/-!
# Buffer order and routing for E.4

The induction invariant says that every allocated buffer above another
allocated buffer is open. It supplies routing definedness without assuming
an actual following probe or a successful `put` result.
-/

namespace Incr.IncrPP

/-- An EOF buffer has no lower allocated buffer. -/
def BufferOrder (buffers : FMap Nat Chunk) : Prop :=
  ∀ i j left right, i < j → FMap.get buffers i = some left →
    FMap.get buffers j = some right → right.flag = .open

/-- No buffer violates order in an empty allocation. -/
theorem BufferOrder.empty : BufferOrder (∅ : FMap Nat Chunk) := by
  intro i j left right less lookup
  simp [FMap.get] at lookup

/-- Removing an allocated slot preserves the order of all surviving buffers. -/
theorem BufferOrder.erase {buffers : FMap Nat Chunk} (ordered : BufferOrder buffers) (slot : Nat) :
    BufferOrder (buffers ∖ slot) := by
  intro i j left right less leftLookup rightLookup
  have leftNe : i ≠ slot := by
    intro equal
    subst i
    simp only [FMap.get_erase_self] at leftLookup
    contradiction
  have rightNe : j ≠ slot := by
    intro equal
    subst j
    simp only [FMap.get_erase_self] at rightLookup
    contradiction
  rw [FMap.get_erase_of_ne leftNe] at leftLookup
  rw [FMap.get_erase_of_ne rightNe] at rightLookup
  exact ordered i j left right less leftLookup rightLookup

/-- Replacing an existing buffer by an open chunk preserves order. -/
theorem BufferOrder.set_existing_open {buffers : FMap Nat Chunk} (ordered : BufferOrder buffers)
    {slot : Nat} {old chunk : Chunk} (present : FMap.get buffers slot = some old)
    (openFlag : chunk.flag = .open) : BufferOrder (buffers[slot ↦ chunk]) := by
  intro i j left right less leftLookup rightLookup
  by_cases atRight : j = slot
  · subst j
    rw [FMap.get_set_self] at rightLookup
    have equal := Option.some.inj rightLookup
    rw [← equal]
    exact openFlag
  · rw [FMap.get_set_other atRight] at rightLookup
    by_cases atLeft : i = slot
    · subst i
      exact ordered slot j old right less present rightLookup
    · rw [FMap.get_set_other atLeft] at leftLookup
      exact ordered i j left right less leftLookup rightLookup

/-- An absent or open successor suffices for routing any output chunk. -/
theorem put_defined_of_successor_open (buffers : FMap Nat Chunk) (slot : Nat) (output : Chunk)
    (safe : ∀ chunk, FMap.get buffers (slot + 1) = some chunk → chunk.flag = .open) :
    ∃ next returned, put buffers slot output = some (next, returned) := by
  unfold put
  cases lookup : FMap.get buffers (slot + 1) with
  | none => exact ⟨buffers, some output, rfl⟩
  | some chunk =>
    rcases chunk with ⟨bytes, flag⟩
    have openFlag : flag = .open := safe _ lookup
    subst flag
    exact ⟨buffers[(slot + 1) ↦ ⟨bytes ++ output.bytes, output.flag⟩], none, rfl⟩

/-- An allocated source forces its successor to be open when the successor exists. -/
theorem put_defined_of_bufferOrder {buffers : FMap Nat Chunk} (ordered : BufferOrder buffers)
    {slot : Nat} {current : Chunk} (present : FMap.get buffers slot = some current) (output : Chunk) :
    ∃ next returned, put buffers slot output = some (next, returned) := by
  apply put_defined_of_successor_open
  intro chunk lookup
  exact ordered slot (slot + 1) current chunk (Nat.lt_succ_self slot) present lookup

/-- Closing erases only the source slot, not its open successor. -/
theorem put_close_defined_of_bufferOrder {buffers : FMap Nat Chunk} (ordered : BufferOrder buffers)
    {slot : Nat} {current : Chunk} (present : FMap.get buffers slot = some current) (output : Chunk) :
    ∃ next returned, put (buffers ∖ slot) slot output = some (next, returned) := by
  apply put_defined_of_successor_open
  intro chunk lookup
  rw [FMap.get_erase_of_ne (Nat.ne_of_gt (Nat.lt_succ_self slot))] at lookup
  exact ordered slot (slot + 1) current chunk (Nat.lt_succ_self slot) present lookup

/-- Updating the consumed source chunk also leaves its successor unchanged. -/
theorem put_open_defined_of_bufferOrder {buffers : FMap Nat Chunk} (ordered : BufferOrder buffers)
    {slot : Nat} {current : Chunk} (present : FMap.get buffers slot = some current)
    (remaining output : Chunk) :
    ∃ next returned, put (buffers[slot ↦ remaining]) slot output = some (next, returned) := by
  apply put_defined_of_successor_open
  intro chunk lookup
  rw [FMap.get_set_other (Nat.ne_of_gt (Nat.lt_succ_self slot))] at lookup
  exact ordered slot (slot + 1) current chunk (Nat.lt_succ_self slot) present lookup

/-- A changed buffer must be open only when a lower allocated slot remains. -/
theorem BufferOrder.set_existing {buffers : FMap Nat Chunk} (ordered : BufferOrder buffers)
    {slot : Nat} {old chunk : Chunk} (present : FMap.get buffers slot = some old)
    (lower : ∀ i left, i < slot → FMap.get buffers i = some left → chunk.flag = .open) :
    BufferOrder (buffers[slot ↦ chunk]) := by
  intro i j left right less leftLookup rightLookup
  by_cases atRight : j = slot
  · subst j
    rw [FMap.get_set_self] at rightLookup
    have equal := Option.some.inj rightLookup
    rw [← equal]
    rw [FMap.get_set_other (Nat.ne_of_lt less)] at leftLookup
    exact lower i left less leftLookup
  · rw [FMap.get_set_other atRight] at rightLookup
    by_cases atLeft : i = slot
    · subst i
      exact ordered slot j old right less present rightLookup
    · rw [FMap.get_set_other atLeft] at leftLookup
      exact ordered i j left right less leftLookup rightLookup

/-- All initialized buffers above slot zero are empty and open. -/
theorem BufferOrder.initial {sig : Signature} (init : PipelineInit sig) :
    BufferOrder (initialBuffers init) := by
  intro i j left right less leftLookup rightLookup
  rw [FMap.get, initialBuffers, Finmap.dlookup_list_toFinmap] at rightLookup
  have member := List.of_mem_dlookup rightLookup
  obtain ⟨pos, bound, equal⟩ := List.mem_mapIdx.mp member
  have index : pos = j := congrArg Sigma.fst equal
  subst pos
  have value : (if j = 0 then init.input else Chunk.emptyOpen) = right := by
    simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using equal
  have nonzero : j ≠ 0 := Nat.ne_of_gt (Nat.lt_of_le_of_lt (Nat.zero_le i) less)
  simpa [nonzero, Chunk.emptyOpen] using (congrArg Chunk.flag value).symm

/-- Routing preserves order when any lower surviving buffer forces an open output. -/
theorem BufferOrder.put {buffers next : FMap Nat Chunk} {slot : Nat} {output : Chunk}
    {returned : Option Chunk} (ordered : BufferOrder buffers)
    (routed : Incr.put buffers slot output = some (next, returned))
    (lower : ∀ i left, i < slot + 1 → FMap.get buffers i = some left → output.flag = .open) :
    BufferOrder next := by
  cases lookup : FMap.get buffers (slot + 1) with
  | none =>
    simp only [Incr.put, lookup, Option.some.injEq, Prod.mk.injEq] at routed
    obtain ⟨rfl, rfl⟩ := routed
    exact ordered
  | some chunk =>
    rcases chunk with ⟨bytes, flag⟩
    cases flag with
    | «open» =>
      simp only [Incr.put, lookup, Option.some.injEq, Prod.mk.injEq] at routed
      obtain ⟨rfl, rfl⟩ := routed
      exact ordered.set_existing lookup lower
    | eof => simp [Incr.put, lookup] at routed

/-- Routing an open chunk preserves order at every allocated slot. -/
theorem BufferOrder.put_open {buffers next : FMap Nat Chunk} {slot : Nat} {output : Chunk}
    {returned : Option Chunk} (ordered : BufferOrder buffers) (openFlag : output.flag = .open)
    (routed : Incr.put buffers slot output = some (next, returned)) : BufferOrder next :=
  ordered.put routed (fun _ _ _ _ => openFlag)

/-- Delivery at slot zero can append either flag without introducing a lower slot. -/
theorem BufferOrder.deliver {buffers : FMap Nat Chunk} (ordered : BufferOrder buffers)
    {old : Chunk} (present : FMap.get buffers 0 = some old) (chunk : Chunk) :
    BufferOrder (buffers[0 ↦ chunk]) := by
  apply ordered.set_existing present
  intro i left less lookup
  exact False.elim (Nat.not_lt_zero i less)

/-- An EOF source excludes lower survivors before routing the closing output. -/
theorem BufferOrder.put_close {buffers next : FMap Nat Chunk} {slot : Nat} {output current : Chunk}
    {returned : Option Chunk} (ordered : BufferOrder buffers)
    (present : FMap.get buffers slot = some current) (eofFlag : current.flag = .eof)
    (routed : Incr.put (buffers ∖ slot) slot output = some (next, returned)) : BufferOrder next := by
  apply (ordered.erase slot).put routed
  intro i left less lookup
  have different : i ≠ slot := by
    intro equal
    subst i
    simp only [FMap.get_erase_self] at lookup
    contradiction
  rw [FMap.get_erase_of_ne different] at lookup
  have before : i < slot := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp less) different
  have openFlag := ordered i slot left current before lookup present
  cases eofFlag.symm.trans openFlag

/-- Initialization and external input delivery preserve order for every permitted selection. -/
theorem BufferOrder.selection {sig : Signature} {m : CommandModel sig} {h : Host sig}
    {executor : Executor} {prog : sig.Prog} (trace : Trace m h executor prog)
    (before : World sig) (selection : Selection sig) (selected : World sig)
    (ordered : BufferOrder before.buffer)
    (discipline : SelectionDiscipline trace before selection selected)
    (delivery : InputDelivery before selection selected) : BufferOrder selected.buffer := by
  rcases discipline with ⟨_, _, _, allocation, _⟩
  cases init : selection.init with
  | some entry =>
    simp only [init] at allocation
    rw [allocation.2.2.2.1]
    exact BufferOrder.initial entry
  | none =>
    simp only [InputDelivery, init] at delivery
    cases annotation : selection.delivery with
    | none =>
      simp only [annotation] at delivery
      rw [delivery]
      exact ordered
    | some chunk =>
      simp only [annotation] at delivery
      obtain ⟨bytes, present, equal⟩ := delivery
      rw [equal]
      exact ordered.deliver present _

/-- All seven live and three vanilla branches preserve the buffer-order invariant. -/
theorem ProbeDerivation.bufferOrder {sig : Signature} {m : CommandModel sig}
    {executor : Executor} {before after : World sig} {head : Head sig} {returned : Option Chunk}
    (d : ProbeDerivation m executor before head after returned) (ordered : BufferOrder before.buffer) :
    BufferOrder after.buffer := by
  cases executor <;> cases d
  all_goals first
    | exact ordered
    | exact ordered.put_close (by assumption) rfl (by assumption)
    | exact (ordered.set_existing_open (by assumption) rfl).put_open (by assumption) (by assumption)

/-- Actual operational prefixes satisfy buffer order from the initial empty maps. -/
theorem Operational.bufferOrder {sig : Signature} {m : CommandModel sig} {h : Host sig}
    {executor : Executor} {prog : sig.Prog} {start : World sig} (host : HostWellFormed m h)
    (pre : Prefix m h executor prog start) (operational : Operational pre) : BufferOrder pre.final.buffer := by
  apply Operational.snoc_induction (fun pre => BufferOrder pre.final.buffer) ?_ ?_ pre operational
  · intro pre _ empty
    have connected := pre.connected
    rw [empty] at connected
    have endpoint := (Connected.nil_iff start pre.final).mp connected
    rw [endpoint, pre.initial.1]
    exact BufferOrder.empty
  · intro short pre d shortOperational _ joined before after ih
    have allowed : h.select prog short.final d.selection d.selected := by
      simpa only [before] using d.host
    have discipline := host.selectionDiscipline executor prog start short shortOperational
      d.selection d.selected allowed
    have delivery := host.inputDelivery executor prog start short shortOperational
      d.selection d.selected allowed
    have selectedOrder := BufferOrder.selection short.trace short.final d.selection d.selected
      ih discipline delivery
    rw [after]
    exact d.probe.bufferOrder selectedOrder

/-- Buffer order also holds after any permitted selection, without a following probe. -/
theorem Boundary.bufferOrder {sig : Signature} {m : CommandModel sig} {h : Host sig}
    {executor : Executor} {prog : sig.Prog} {start : World sig} (host : HostWellFormed m h)
    (pre : Prefix m h executor prog start) (operational : Operational pre) (b : Boundary pre) :
    BufferOrder b.world.buffer := by
  cases b with
  | final => exact Operational.bufferOrder host pre operational
  | selected selection world allowed =>
    exact BufferOrder.selection pre.trace pre.final selection world
      (Operational.bufferOrder host pre operational)
      (host.selectionDiscipline executor prog start pre operational selection world allowed)
      (host.inputDelivery executor prog start pre operational selection world allowed)

end IncrPP
end Incr
