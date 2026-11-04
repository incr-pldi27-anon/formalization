import Incr.Incr.Preservation.Buffers

/-! # Joint buffer, sandbox, history, closure, and routing preservation -/

open Incr
namespace Incr.Incr.BufferPreservation

noncomputable section

variable {sig : Signature} {m : CommandModel sig} {h : Host sig}
  {executor : Executor} {prog : sig.Prog}

def Fields (trace : Trace m h executor prog) (entry i : Nat) (sb : Sandbox sig) : Prop :=
  match executor with
  | .incr => HistoryAccumulation sb.base (openHistory trace (.pipeline entry i)) sb
  | .vanilla => sb = Sandbox.initial sb.base

/-- Snapshot data at the selection boundary, before the new probe runs. -/
def Snapshots (trace : Trace m h executor prog) (d : StepDerivation m h executor prog) : Prop :=
  ∀ i sb, FMap.get d.selected.sandbox i = some sb →
    ∃ entry init entryStep,
      selectedPipeline trace d.selection = some (entry, init) ∧
      (trace ++ [d])[entry]? = some entryStep ∧ entryStep.selection.init = some init ∧
      sb.base = entryStep.before.fs ∧
      Fields trace entry i sb

/-- Slot membership at the selection boundary uses the incoming histories. -/
def Slots (trace : Trace m h executor prog) (d : StepDerivation m h executor prog) : Prop :=
  ∀ entry init, selectedPipeline trace d.selection = some (entry, init) →
    ∀ i, i ∈ FMap.dom d.selected.sandbox ↔
      i < init.probes.length ∧ ¬ slotClosed trace entry i

theorem snapshots_selection {trace : Trace m h executor prog} {w : World sig}
    (state : SandboxState trace w) (d : StepDerivation m h executor prog)
    (he : w = d.before) (hd : SelectionDiscipline trace w d.selection d.selected) :
    Snapshots trace d := by
  intro i sb hs
  rcases hd with ⟨_, _, _, hi, _⟩
  cases hp : d.selection.init with
  | none =>
      simp only [hp] at hi
      obtain ⟨entry, init, entryStep, latest, hentry, hinit, hbase, hist⟩ :=
        state.2.1 i sb (by simpa [hi.1] using hs)
      refine ⟨entry, init, entryStep, by simpa [selectedPipeline, hp] using latest, ?_, hinit, hbase, ?_⟩
      · have hb := (List.getElem?_eq_some_iff.mp hentry).1
        simpa [List.getElem?_append, hb] using hentry
      · cases executor <;> exact hist
  | some init =>
      simp only [hp] at hi
      rw [hi.2.2.2.2] at hs
      have hsb := initialSandboxes_get_eq init w.fs hs
      subst sb
      refine ⟨trace.length, init, d, by simp [selectedPipeline, hp], by simp, hp, ?_, ?_⟩
      · simpa [Sandbox.initial] using congrArg World.fs he
      · have hempty : openHistory trace (.pipeline trace.length i) = [] := by
          simp [openHistory, componentSteps_future_entry trace i (Nat.le_refl _)]
        cases executor with
        | incr =>
            change HistoryAccumulation w.fs _ _
            rw [hempty]
            exact .nil
        | vanilla => rfl

theorem slots_selection {trace : Trace m h executor prog} {w : World sig}
    (state : SandboxState trace w) (d : StepDerivation m h executor prog)
    (hd : SelectionDiscipline trace w d.selection d.selected) : Slots trace d := by
  intro entry init latest i
  rcases hd with ⟨_, _, _, hi, _⟩
  cases hp : d.selection.init with
  | none =>
      simp only [hp] at hi
      simp only [selectedPipeline, hp] at latest
      rw [hi.1]
      exact state.2.2.2.1 entry init latest i
  | some init' =>
      simp only [selectedPipeline, hp, Option.some.injEq, Prod.mk.injEq] at latest
      obtain ⟨rfl, rfl⟩ := latest
      simp only [hp] at hi
      rw [hi.2.2.2.2]
      simp [initialSandboxes, mapIdx_toFinmap_dom, slotClosed,
        componentSteps_future_entry trace i (Nat.le_refl _)]

theorem pipeline_effect {w w' : World sig} {head : Head sig} {out : Option Chunk}
    (probe : ProbeDerivation m executor w head w' out) (p : sig.Probe) (i : Nat)
    (hh : head = .pipeline p i) :
    if (ProbeDerivation.input probe).flag = .open then
      match executor with
      | .incr => ∃ sb hi ho, FMap.get w.sandbox i = some sb ∧
          w'.sandbox = w.sandbox[i ↦ (sb.accumulate
            (ProbeDerivation.input probe) (ProbeDerivation.result probe) hi ho)]
      | .vanilla => w'.sandbox = w.sandbox
    else w'.sandbox = w.sandbox ∖ i := by
  cases hh
  cases executor <;> cases probe <;>
    simp only [ProbeDerivation.input, ProbeDerivation.result, IncrDerivation.input,
      IncrDerivation.result, VanillaDerivation.input,
      reduceCtorEq, ite_true, ite_false, closeWorld, updateWorld]
  exact ⟨_, _, _, by assumption, rfl⟩

theorem standalone_effect {w w' : World sig} {head : Head sig} {out : Option Chunk}
    (probe : ProbeDerivation m executor w head w' out) (p : sig.Probe)
    (hh : head = .standalone p) : w'.sandbox = w.sandbox ∧
      (ProbeDerivation.input probe).flag = .eof := by
  cases hh
  cases executor <;> cases probe <;>
    simp [ProbeDerivation.input, IncrDerivation.input, VanillaDerivation.input, standaloneWorld]

theorem snapshots_after {trace : Trace m h executor prog}
    (d : StepDerivation m h executor prog) (snap : Snapshots trace d) :
    ∀ i sb, FMap.get d.after.sandbox i = some sb →
      ∃ entry init entryStep,
        latestPipeline (trace ++ [d]) = some (entry, init) ∧
        (trace ++ [d])[entry]? = some entryStep ∧ entryStep.selection.init = some init ∧
        sb.base = entryStep.before.fs ∧
        Fields (trace ++ [d]) entry i sb := by
  intro i sb hs
  have unchanged (hs' : FMap.get d.selected.sandbox i = some sb)
      (history : ∀ entry init, selectedPipeline trace d.selection = some (entry, init) →
        openHistory (trace ++ [d]) (.pipeline entry i) = openHistory trace (.pipeline entry i)) :
      ∃ entry init entryStep,
        latestPipeline (trace ++ [d]) = some (entry, init) ∧
        (trace ++ [d])[entry]? = some entryStep ∧ entryStep.selection.init = some init ∧
        sb.base = entryStep.before.fs ∧
        Fields (trace ++ [d]) entry i sb := by
    obtain ⟨entry, init, e, hl, he, hi, hb, hist⟩ := snap i sb hs'
    refine ⟨entry, init, e, by simpa [latestPipeline_snoc] using hl, he, hi, hb, ?_⟩
    cases executor with
    | incr =>
        change HistoryAccumulation sb.base _ _
        rw [history entry init hl]
        exact hist
    | vanilla => exact hist
  cases hh : d.selection.head with
  | standalone p =>
      have effect := standalone_effect d.probe p hh
      apply unchanged (by simpa [effect.1] using hs)
      intro entry init hl
      simp [openHistory_snoc, effect.2]
  | pipeline p j =>
      have effect := pipeline_effect d.probe p j hh
      by_cases hopen : (ProbeDerivation.input d.probe).flag = .open
      · simp only [hopen, ite_true] at effect
        cases executor with
        | vanilla =>
            obtain ⟨entry, init, e, hl, he, hi, hb, hist⟩ := snap i sb (by simpa [effect] using hs)
            exact ⟨entry, init, e, by simpa [latestPipeline_snoc] using hl, he, hi, hb, hist⟩
        | incr =>
            obtain ⟨old, hi, ho, hold, heffect⟩ := effect
            rw [heffect] at hs
            by_cases hij : i = j
            · subst i
              rw [FMap.get_set_self] at hs
              cases Option.some.inj hs
              obtain ⟨entry, init, e, hl, he, hin, hb, hist⟩ := snap j old hold
              refine ⟨entry, init, e, by simpa [latestPipeline_snoc] using hl, he, hin, hb, ?_⟩
              have hc : componentAt (trace ++ [d]) trace.length d = some (.pipeline entry j) := by
                simp [componentAt_snoc_last, hh, selectedComponent, hl]
              change HistoryAccumulation old.base _ _
              simpa only [openHistory_snoc, hc, hopen, eq_self, and_self, ite_true] using
                (HistoryAccumulation.snoc _ old d hist hi ho hopen)
            · rw [FMap.get_set_other hij] at hs
              apply unchanged hs
              intro entry init hl
              have hc : componentAt (trace ++ [d]) trace.length d = some (.pipeline entry j) := by
                simp [componentAt_snoc_last, hh, selectedComponent, hl]
              simp [openHistory_snoc, hc, Ne.symm hij]
      · simp only [hopen, ite_false] at effect
        rw [effect] at hs
        by_cases hij : i = j
        · subst i
          rw [FMap.get_erase_self] at hs
          contradiction
        · rw [FMap.get_erase_of_ne hij] at hs
          apply unchanged hs
          intro entry init hl
          simp [openHistory_snoc, hopen]

theorem mem_dom_iff {K V : Type} [DecidableEq K] (map : FMap K V) (i : K) :
    i ∈ FMap.dom map ↔ ∃ v, FMap.get map i = some v := by
  constructor
  · intro hi
    exact Finmap.mem_iff.mp (Finmap.mem_keys.mpr hi)
  · intro hi
    exact Finmap.mem_keys.mp (Finmap.mem_iff.mpr hi)

theorem successors_selection {trace : Trace m h executor prog} {w : World sig}
    (state : SandboxState trace w) (d : StepDerivation m h executor prog)
    (hd : SelectionDiscipline trace w d.selection d.selected) :
    ∀ entry init, selectedPipeline trace d.selection = some (entry, init) →
      ∀ i, i + 1 < init.probes.length → i ∈ FMap.dom d.selected.sandbox →
        i + 1 ∈ FMap.dom d.selected.sandbox := by
  intro entry init latest i bound present
  rcases hd with ⟨_, _, _, hi, _⟩
  cases hp : d.selection.init with
  | none =>
      simp only [hp] at hi
      simp only [selectedPipeline, hp] at latest
      rw [hi.1] at present ⊢
      exact state.2.2.2.2.2.1 entry init latest i bound present
  | some init' =>
      simp only [selectedPipeline, hp, Option.some.injEq, Prod.mk.injEq] at latest
      obtain ⟨rfl, rfl⟩ := latest
      simp only [hp] at hi
      rw [hi.2.2.2.2]
      simpa [initialSandboxes, mapIdx_toFinmap_dom] using bound

theorem closed_downward {trace : Trace m h executor prog}
    (order : ClosingOrder trace) {entry j : Nat} (closed : slotClosed trace entry j)
    (i : Nat) (hi : i < j) : slotClosed trace entry i := by
  obtain ⟨pos, d, hp, hc, hf⟩ := (slotClosed_iff_position trace entry j).mp closed
  obtain ⟨earlier, previous, _, he, hk, hflag⟩ := order pos d entry j hp hc hf i hi
  exact (slotClosed_iff_position trace entry i).mpr ⟨earlier, previous, he, hk, hflag⟩

theorem source_buffer {w w' : World sig} {head : Head sig} {out : Option Chunk}
    (probe : ProbeDerivation m executor w head w' out) (p : sig.Probe) (i : Nat)
    (hh : head = .pipeline p i) :
    ∃ bytes, FMap.get w.buffer i = some ⟨bytes, (ProbeDerivation.input probe).flag⟩ := by
  cases hh
  cases executor <;> cases probe <;>
    simp only [ProbeDerivation.input, IncrDerivation.input, VanillaDerivation.input]
  all_goals exact ⟨_, by assumption⟩

theorem pipeline_membership {w w' : World sig} {head : Head sig} {out : Option Chunk}
    (probe : ProbeDerivation m executor w head w' out) (p : sig.Probe) (j : Nat)
    (hh : head = .pipeline p j) (i : Nat) :
    i ∈ FMap.dom w'.sandbox ↔ i ∈ FMap.dom w.sandbox ∧
      ¬ (i = j ∧ (ProbeDerivation.input probe).flag = .eof) := by
  have effect := pipeline_effect probe p j hh
  cases hf : (ProbeDerivation.input probe).flag with
  | «open» =>
      simp only [hf, ite_true] at effect
      cases executor with
      | incr =>
          obtain ⟨sb, hi, ho, hs, he⟩ := effect
          rw [he, FMap.dom_set_of_get _ _ _ ⟨sb, hs⟩]
          simp
      | vanilla => simp [effect]
  | eof =>
      simp only [hf, reduceCtorEq, ite_false] at effect
      simp [effect, FMap.dom_erase]

theorem lower_closed {trace : Trace m h executor prog}
    (d : StepDerivation m h executor prog) (slots : Slots trace d)
    (domains : FMap.dom d.selected.buffer = FMap.dom d.selected.sandbox)
    (buffers : BufferOrder d.selected.buffer) (order : ClosingOrder trace)
    {entry : Nat} {init : PipelineInit sig}
    (latest : selectedPipeline trace d.selection = some (entry, init))
    {p : sig.Probe} {j : Nat} (hh : d.selection.head = .pipeline p j)
    (present : j ∈ FMap.dom d.selected.sandbox)
    (eof : (ProbeDerivation.input d.probe).flag = .eof) :
    ∀ i, i < j → slotClosed trace entry i := by
  cases j with
  | zero => intro i hi; omega
  | succ j =>
      have bound := ((slots entry init latest (j + 1)).mp present).1
      obtain ⟨bytes, source⟩ := source_buffer d.probe p (j + 1) hh
      rw [eof] at source
      have previous : slotClosed trace entry j := by
        by_contra hnot
        have hp : j ∈ FMap.dom d.selected.sandbox :=
          (slots entry init latest j).mpr ⟨by omega, hnot⟩
        rw [← domains] at hp
        obtain ⟨b, hb⟩ := (mem_dom_iff _ _).mp hp
        have impossible := buffers j b ⟨bytes, .eof⟩ hb source
        contradiction
      intro i hi
      by_cases hij : i = j
      · simpa [hij] using previous
      · exact closed_downward order previous i (by omega)

theorem last_pipeline {trace : Trace m h executor prog}
    (d : StepDerivation m h executor prog) (entry j : Nat) :
    componentAt (trace ++ [d]) trace.length d = some (.pipeline entry j) ↔
      ∃ p init, d.selection.head = .pipeline p j ∧
        selectedPipeline trace d.selection = some (entry, init) := by
  rw [componentAt_snoc_last]
  cases hh : d.selection.head with
  | standalone p => simp
  | pipeline p i =>
      simp only [selectedComponent]
      cases hl : selectedPipeline trace d.selection with
      | none => simp
      | some pair =>
          obtain ⟨e, init⟩ := pair
          simp [eq_comm, and_comm]

theorem selected_present {trace : Trace m h executor prog} {w : World sig}
    (d : StepDerivation m h executor prog)
    (hd : SelectionDiscipline trace w d.selection d.selected)
    {p : sig.Probe} {j : Nat} (hh : d.selection.head = .pipeline p j) :
    j ∈ FMap.dom d.selected.sandbox := by
  have head := hd.2.2.2.2
  simp only [hh] at head
  exact head.2.2.1

theorem slots_after {trace : Trace m h executor prog}
    (d : StepDerivation m h executor prog) (slots : Slots trace d) :
    ∀ entry init, latestPipeline (trace ++ [d]) = some (entry, init) →
      ∀ i, i ∈ FMap.dom d.after.sandbox ↔
        i < init.probes.length ∧ ¬ slotClosed (trace ++ [d]) entry i := by
  intro entry init latest i
  rw [latestPipeline_snoc] at latest
  cases hh : d.selection.head with
  | standalone p =>
      have effect := standalone_effect d.probe p hh
      have hc : componentAt (trace ++ [d]) trace.length d = some (.standalone trace.length) := by
        simp [componentAt_snoc_last, hh]
      simpa [effect.1, slotClosed_snoc, hc] using slots entry init latest i
  | pipeline p j =>
      have hc : componentAt (trace ++ [d]) trace.length d = some (.pipeline entry j) := by
        simp [componentAt_snoc_last, hh, selectedComponent, latest]
      rw [pipeline_membership d.probe p j hh i, slots entry init latest i, slotClosed_snoc]
      simp only [hc, Option.some.injEq, Component.pipeline.injEq, true_and]
      tauto

theorem closing_after {trace : Trace m h executor prog} {w : World sig}
    (d : StepDerivation m h executor prog) (slots : Slots trace d)
    (domains : FMap.dom d.selected.buffer = FMap.dom d.selected.sandbox)
    (buffers : BufferOrder d.selected.buffer) (order : ClosingOrder trace)
    (hd : SelectionDiscipline trace w d.selection d.selected) : ClosingOrder (trace ++ [d]) := by
  apply order.snoc d
  intro entry j hc eof i hij
  obtain ⟨p, init, hh, latest⟩ := (last_pipeline d entry j).mp hc
  exact lower_closed d slots domains buffers order latest hh
    (selected_present d hd hh) eof i hij

theorem successors_after {trace : Trace m h executor prog} {w : World sig}
    (d : StepDerivation m h executor prog) (slots : Slots trace d)
    (domains : FMap.dom d.selected.buffer = FMap.dom d.selected.sandbox)
    (buffers : BufferOrder d.selected.buffer) (order : ClosingOrder trace)
    (hd : SelectionDiscipline trace w d.selection d.selected)
    (successors : ∀ entry init, selectedPipeline trace d.selection = some (entry, init) →
      ∀ i, i + 1 < init.probes.length → i ∈ FMap.dom d.selected.sandbox →
        i + 1 ∈ FMap.dom d.selected.sandbox) :
    ∀ entry init, latestPipeline (trace ++ [d]) = some (entry, init) →
      ∀ i, i + 1 < init.probes.length → i ∈ FMap.dom d.after.sandbox →
        i + 1 ∈ FMap.dom d.after.sandbox := by
  intro entry init latest i bound present
  rw [latestPipeline_snoc] at latest
  cases hh : d.selection.head with
  | standalone p =>
      have effect := (standalone_effect d.probe p hh).1
      rw [effect] at present ⊢
      exact successors entry init latest i bound present
  | pipeline p j =>
      have before := ((pipeline_membership d.probe p j hh i).mp present).1
      rw [pipeline_membership d.probe p j hh (i + 1)]
      refine ⟨successors entry init latest i bound before, ?_⟩
      rintro ⟨hij, eof⟩
      have closed := lower_closed d slots domains buffers order latest hh
        (selected_present d hd hh) eof i (by omega)
      exact ((slots entry init latest i).mp before).2 closed

theorem routing_successor {w w' : World sig} {head : Head sig} {out : Option Chunk}
    (probe : ProbeDerivation m executor w head w' out) (p : sig.Probe) (i : Nat)
    (hh : head = .pipeline p i) {buffers : FMap Nat Chunk}
    (hb : ProbeDerivation.routingBuffers probe = some buffers) :
    FMap.get buffers (i + 1) = FMap.get w.buffer (i + 1) := by
  have hne : i + 1 ≠ i := by omega
  cases hh
  cases executor <;> cases probe <;>
    simp only [ProbeDerivation.routingBuffers, Option.some.injEq] at hb
  all_goals rw [← hb]
  all_goals first
  | exact FMap.get_set_other hne
  | exact FMap.get_erase_of_ne hne

theorem put_some_no_successor {buffers routed : FMap Nat Chunk} {slot : Nat}
    {output : Chunk} {out : Option Chunk}
    (hp : put buffers slot output = some (routed, out)) (some : out.isSome) :
    FMap.get buffers (slot + 1) = none := by
  unfold put at hp
  cases hn : FMap.get buffers (slot + 1) with
  | none => rfl
  | some next =>
      cases next with
      | mk bytes flag =>
          cases flag with
          | eof => simp [hn] at hp
          | «open» =>
              simp only [hn, Option.some.injEq, Prod.mk.injEq] at hp
              obtain ⟨rfl, rfl⟩ := hp
              contradiction

theorem terminal_slot {trace : Trace m h executor prog}
    (d : StepDerivation m h executor prog) (slots : Slots trace d)
    (domains : FMap.dom d.selected.buffer = FMap.dom d.selected.sandbox)
    (successors : ∀ entry init, selectedPipeline trace d.selection = some (entry, init) →
      ∀ i, i + 1 < init.probes.length → i ∈ FMap.dom d.selected.sandbox →
        i + 1 ∈ FMap.dom d.selected.sandbox)
    {entry : Nat} {init : PipelineInit sig}
    (latest : selectedPipeline trace d.selection = some (entry, init))
    {p : sig.Probe} {i : Nat} (hh : d.selection.head = .pipeline p i)
    (present : i ∈ FMap.dom d.selected.sandbox) (returned : d.out.isSome) :
    i + 1 = init.probes.length := by
  have bound := ((slots entry init latest i).mp present).1
  obtain ⟨buffers, hb, hp⟩ := d.probe.routingBuffers_pipeline p i hh
  have absent := put_some_no_successor hp returned
  rw [routing_successor d.probe p i hh hb] at absent
  have last : ¬ i + 1 < init.probes.length := by
    intro hlt
    have successor := successors entry init latest i hlt present
    rw [← domains] at successor
    obtain ⟨next, hnext⟩ := (mem_dom_iff _ _).mp successor
    rw [absent] at hnext
    contradiction
  omega

theorem routing_after {trace : Trace m h executor prog} {w : World sig}
    (d : StepDerivation m h executor prog) (previous : RoutingReady trace)
    (snap : Snapshots trace d) (slots : Slots trace d)
    (domains : FMap.dom d.selected.buffer = FMap.dom d.selected.sandbox)
    (hd : SelectionDiscipline trace w d.selection d.selected)
    (successors : ∀ entry init, selectedPipeline trace d.selection = some (entry, init) →
      ∀ i, i + 1 < init.probes.length → i ∈ FMap.dom d.selected.sandbox →
        i + 1 ∈ FMap.dom d.selected.sandbox) : RoutingReady (trace ++ [d]) := by
  intro pos e p i hp hh
  have hpos : pos < trace.length + 1 := by
    have := (List.getElem?_eq_some_iff.mp hp).1
    simpa using this
  by_cases hlt : pos < trace.length
  · have he : (trace)[pos]? = some e := by
      simpa [List.getElem?_append, hlt] using hp
    obtain ⟨entry, init, latest, routed, terminal⟩ := previous pos e p i he hh
    refine ⟨entry, init, ?_, routed, terminal⟩
    simpa [List.take_append_of_le_length (show pos + 1 ≤ trace.length by omega)] using latest
  · have heq : pos = trace.length := by omega
    subst pos
    have hed : e = d := by simpa using hp.symm
    subst e
    have present := selected_present d hd hh
    obtain ⟨sb, hs⟩ := (mem_dom_iff _ _).mp present
    obtain ⟨entry, init, _, latest, _⟩ := snap i sb hs
    refine ⟨entry, init, ?_, ?_, terminal_slot d slots domains successors latest hh present⟩
    · have ht : (trace ++ [d]).take (trace.length + 1) = trace ++ [d] := by
        apply List.take_of_length_le
        simp
      simpa [ht, latestPipeline_snoc] using latest
    · obtain ⟨buffers, hb, hp⟩ := d.probe.routingBuffers_pipeline p i hh
      exact ⟨buffers, d.after.buffer, d.out, hb, hp⟩

theorem state_after {trace : Trace m h executor prog} {w : World sig}
    (state : SandboxState trace w) (d : StepDerivation m h executor prog)
    (he : w = d.before) (hd : SelectionDiscipline trace w d.selection d.selected)
    (delivery : InputDelivery w d.selection d.selected) : SandboxState (trace ++ [d]) d.after := by
  have domains := hd.domains state.1
  have buffers := hd.bufferOrder delivery state.2.2.1
  have snap := snapshots_selection state d he hd
  have slots := slots_selection state d hd
  have successors := successors_selection state d hd
  have order := state.2.2.2.2.2.2
  refine ⟨d.probe.domains domains, ?_, d.probe.bufferOrder buffers,
    slots_after d slots, ?_, successors_after d slots domains buffers order hd successors,
    closing_after d slots domains buffers order hd⟩
  · intro i sb hs
    obtain ⟨entry, init, e, hl, he, hi, hb, hist⟩ := snapshots_after d snap i sb hs
    refine ⟨entry, init, e, hl, he, hi, hb, ?_⟩
    cases executor <;> exact hist
  · intro latest
    rw [latestPipeline_snoc] at latest
    have hinit := hd.2.2.2.1
    cases hp : d.selection.init with
    | some init => simp [selectedPipeline, hp] at latest
    | none =>
        simp only [selectedPipeline, hp] at latest
        simp only [hp] at hinit
        have hempty : FMap.dom d.selected.sandbox = ∅ := by
          rw [hinit.1]
          exact state.2.2.2.2.1 latest
        apply Set.eq_empty_of_subset_empty
        simpa [hempty] using d.probe.sandbox_domain_subset

/-- `lem:paper-buffers` with the production theorem's exact assumptions and
conclusion. -/
theorem preservation {start : World sig}
    (_shape : DenotationShape m) (_commands : WellFormedCommands m)
    (_key : HashInjective m) (host : HostWellFormed m h)
    (pre : Prefix m h executor prog start) (operational : Operational pre) :
    BufferSandboxPreservation pre := by
  change SandboxState pre.trace pre.final ∧ RoutingReady pre.trace
  apply operational.trace_induction (fun trace w => SandboxState trace w ∧ RoutingReady trace)
  · simp [SandboxState, BufferOrder, ClosingOrder, RoutingReady, latestPipeline,
      pre.initial.1, pre.initial.2.1, FMap.get]
  · intro earlier hearlier joint d he
    obtain ⟨state, routing⟩ := joint
    have hd := host.selectionDiscipline executor prog start earlier hearlier
      d.selection d.selected (by simpa [he] using d.host)
    have delivery := host.inputDelivery executor prog start earlier hearlier
      d.selection d.selected (by simpa [he] using d.host)
    exact ⟨state_after state d he hd delivery,
      routing_after d routing (snapshots_selection state d he hd)
        (slots_selection state d hd) (hd.domains state.1) hd
        (successors_selection state d hd)⟩

end

end Incr.Incr.BufferPreservation


