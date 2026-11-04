import Incr.Incr.Preservation.Components

/-! # Local preservation facts for recorded `lem:paper-buffers` -/

open Incr
namespace Incr.Incr

noncomputable section

variable {sig : Signature} {m : CommandModel sig} {h : Host sig}
  {executor : Executor} {prog : sig.Prog}

/-- An open-input rule records an open-output result. -/
theorem history_open_result_flag {w w' : World sig} {head : Head sig} {out : Option Chunk}
    (d : ProbeDerivation m executor w head w' out)
    (hopen : (ProbeDerivation.input d).flag = .open) :
    (ProbeDerivation.result d).output.flag = .open := by
  cases executor <;> cases d <;>
    simp_all [ProbeDerivation.input, ProbeDerivation.result,
      IncrDerivation.input, IncrDerivation.result,
      VanillaDerivation.input, VanillaDerivation.result]

/-- Exact accumulation supplies both open flags without a numbered theorem. -/
theorem HistoryAccumulation.open_flags {base : FS sig} {trace : Trace m h executor prog}
    {sb : Sandbox sig} (hist : HistoryAccumulation base trace sb) :
    sb.input.flag = .open ∧ sb.output.flag = .open := by
  induction hist with
  | nil => exact ⟨rfl, rfl⟩
  | snoc trace sb d previous hi ho hopen ih =>
    exact ⟨hopen, history_open_result_flag d.probe hopen⟩

/-- An empty accumulated history has exactly the initialized fields. -/
theorem HistoryAccumulation.eq_initial {base : FS sig} {trace : Trace m h executor prog}
    {sb : Sandbox sig} (hist : HistoryAccumulation base trace sb)
    (empty : trace = []) : sb = Sandbox.initial base := by
  cases hist with
  | nil => rfl
  | snoc trace sb d previous hi ho hopen => simp at empty

/-- Indexed initialization maps contain exactly the initialized indices. -/
theorem mapIdx_toFinmap_dom {α V : Type} (xs : List α) (f : Nat → α → V) :
    FMap.dom (xs.mapIdx fun i x => (⟨i, f i x⟩ : Sigma (fun _ : Nat => V))).toFinmap =
      {i | i < xs.length} := by
  ext i
  change i ∈ (xs.mapIdx fun i x => (⟨i, f i x⟩ : Sigma (fun _ : Nat => V))).toFinmap ↔ _
  rw [Finmap.mem_list_toFinmap]
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨j, hj, he⟩ := List.mem_mapIdx.mp hv
    have hji : j = i := congrArg Sigma.fst he
    simpa [← hji] using hj
  · intro hi
    exact ⟨f i xs[i], List.mem_mapIdx.mpr ⟨i, hi, rfl⟩⟩

/-- Initialization gives equal buffer and sandbox domains. -/
theorem initial_domains (init : PipelineInit sig) (fs : FS sig) :
    FMap.dom (initialBuffers init) = FMap.dom (initialSandboxes init fs) := by
  simp only [initialBuffers, initialSandboxes, mapIdx_toFinmap_dom]

/-- Every recorded probe rule preserves equality of the two live domains. -/
theorem ProbeDerivation.domains {w w' : World sig} {head : Head sig} {out : Option Chunk}
    (d : ProbeDerivation m executor w head w' out)
    (domains : FMap.dom w.buffer = FMap.dom w.sandbox) :
    FMap.dom w'.buffer = FMap.dom w'.sandbox := by
  cases executor <;> cases d <;> dsimp only [closeWorld, standaloneWorld, updateWorld]
  all_goals first
  | exact domains
  | (rw [put_domain (by assumption)];
      first
      | solve | simp only [FMap.dom_erase, domains]
      | (rw [FMap.dom_set_of_get _ _ _ (by exact ⟨_, by assumption⟩),
             FMap.dom_set_of_get _ _ _ (by exact ⟨_, by assumption⟩)]; exact domains)
      | (rw [FMap.dom_set_of_get _ _ _ (by exact ⟨_, by assumption⟩)]; exact domains))

/-- H1 preserves equal domains at the host-selection boundary. -/
theorem SelectionDiscipline.domains {trace : Trace m h executor prog}
    {before selected : World sig} {selection : Selection sig}
    (hd : SelectionDiscipline trace before selection selected)
    (domains : FMap.dom before.buffer = FMap.dom before.sandbox) :
    FMap.dom selected.buffer = FMap.dom selected.sandbox := by
  rcases hd with ⟨_, _, _, hi, _⟩
  cases hs : selection.init with
  | none =>
      simp only [hs] at hi
      rw [hi.1, hi.2, domains]
  | some init =>
      simp only [hs] at hi
      rw [hi.2.2.2.1, hi.2.2.2.2]
      exact initial_domains init before.fs

private theorem connected_snoc {a b : World sig} {xs : Trace m h executor prog}
    (hc : Connected a xs b) (d : StepDerivation m h executor prog) (he : b = d.before) :
    Connected a (xs ++ [d]) d.after := by
  induction hc with
  | nil => rw [he]; exact .cons d [] d.after (.nil _)
  | cons e rest final ht ih => exact .cons e _ _ (ih he)

/-- Induct over actual connected prefixes, retaining their operational evidence. -/
theorem Operational.trace_induction {start : World sig}
    {full : Prefix m h executor prog start} (hop : Operational full)
    (P : Trace m h executor prog → World sig → Prop)
    (initial : P [] start)
    (step : ∀ (pre : Prefix m h executor prog start), Operational pre → P pre.trace pre.final →
      ∀ d : StepDerivation m h executor prog, pre.final = d.before →
        P (pre.trace ++ [d]) d.after) : P full.trace full.final := by
  have aux : ∀ {w final : World sig} {rest : Trace m h executor prog},
      Connected w rest final → ∀ (pre : Prefix m h executor prog start),
      pre.final = w → (∀ d ∈ pre.trace, d ∈ full.trace) →
      (∀ d ∈ rest, d ∈ full.trace) → P pre.trace pre.final →
      P (pre.trace ++ rest) final := by
    intro w final rest hc
    induction hc with
    | nil => intro pre he _ _ hp; simpa [he] using hp
    | cons d rest final ht ih =>
        intro pre he hpre hrest hp
        have hn := step pre (hop.of_trace_subset hpre) hp d he
        let next : Prefix m h executor prog start :=
          ⟨pre.trace ++ [d], d.after, pre.initial, connected_snoc pre.connected d he⟩
        have hnpre : ∀ e ∈ next.trace, e ∈ full.trace := by
          intro e he
          rcases List.mem_append.mp he with he | he
          · exact hpre e he
          · have hed : e = d := by simpa using he
            subst e
            exact hrest d (by simp)
        have hnrest : ∀ e ∈ rest, e ∈ full.trace := by
          intro e he
          exact hrest e (by simp [he])
        have := ih next rfl hnpre hnrest hn
        simpa only [next, List.append_assoc, List.singleton_append] using this
  let empty : Prefix m h executor prog start := ⟨[], start, full.initial, .nil start⟩
  exact aux full.connected empty rfl (by simp [empty]) (by simp) initial

/-- The live buffer and sandbox domains agree in every operational prefix. -/
theorem Operational.buffer_sandbox_domains {start : World sig}
    {pre : Prefix m h executor prog start} (hop : Operational pre)
    (host : HostWellFormed m h) :
    FMap.dom pre.final.buffer = FMap.dom pre.final.sandbox := by
  apply hop.trace_induction (fun _ w => FMap.dom w.buffer = FMap.dom w.sandbox)
  · simp [pre.initial.1, pre.initial.2.1]
  · intro earlier hearlier domains d he
    have hd := host.selectionDiscipline executor prog start earlier hearlier
      d.selection d.selected (by simpa [he] using d.host)
    have hs := hd.domains domains
    exact d.probe.domains hs

/-- Replacing an existing slot preserves order when its new flag is open,
or when the slot is zero and has no predecessor. -/
theorem BufferOrder.after_set {buffers : FMap Nat Chunk} {slot : Nat} {old new : Chunk}
    (order : BufferOrder buffers) (present : FMap.get buffers slot = some old)
    (ready : slot = 0 ∨ new.flag = .open) : BufferOrder (buffers[slot ↦ new]) := by
  intro i b successor hb hs
  by_cases hi : i + 1 = slot
  · rw [hi, FMap.get_set_self] at hs
    cases Option.some.inj hs
    rcases ready with hz | ho
    · omega
    · exact ho
  · rw [FMap.get_set_other hi] at hs
    by_cases hj : i = slot
    · subst i
      exact order slot old successor present hs
    · rw [FMap.get_set_other hj] at hb
      exact order i b successor hb hs

/-- Routing preserves order for open output or an absent source slot. -/
theorem BufferOrder.after_put {buffers routed : FMap Nat Chunk} {slot : Nat}
    {output : Chunk} {out : Option Chunk} (order : BufferOrder buffers)
    (ready : output.flag = .open ∨ FMap.get buffers slot = none)
    (hp : put buffers slot output = some (routed, out)) : BufferOrder routed := by
  unfold put at hp
  cases hn : FMap.get buffers (slot + 1) with
  | none =>
      simp only [hn, Option.some.injEq, Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      exact order
  | some next =>
    cases next with
    | mk bytes flag =>
      cases flag with
      | eof => simp [hn] at hp
      | «open» =>
        simp only [hn, Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, rfl⟩ := hp
        intro i b successor hb hs
        by_cases hi : i + 1 = slot + 1
        · have hi' : i = slot := by omega
          subst i
          rw [FMap.get_set_self] at hs
          cases Option.some.inj hs
          rcases ready with hopen | absent
          · exact hopen
          · rw [FMap.get_set_other (by omega), absent] at hb
            contradiction
        · rw [FMap.get_set_other hi] at hs
          by_cases hsource : i = slot + 1
          · subst i
            exact order (slot + 1) ⟨bytes, .open⟩ successor hn hs
          · rw [FMap.get_set_other hsource] at hb
            exact order i b successor hb hs

/-- Removing a slot cannot violate order between remaining adjacent slots. -/
theorem BufferOrder.after_erase {buffers : FMap Nat Chunk} (order : BufferOrder buffers)
    (slot : Nat) : BufferOrder (buffers ∖ slot) := by
  intro i b successor hb hs
  by_cases hi : i = slot
  · subst i
    rw [FMap.get_erase_self] at hb
    contradiction
  · rw [FMap.get_erase_of_ne hi] at hb
    by_cases hj : i + 1 = slot
    · rw [hj, FMap.get_erase_self] at hs
      contradiction
    · rw [FMap.get_erase_of_ne hj] at hs
      exact order i b successor hb hs

/-- All recorded probe rules preserve openness of a present successor. -/
theorem ProbeDerivation.bufferOrder {w w' : World sig} {head : Head sig} {out : Option Chunk}
    (d : ProbeDerivation m executor w head w' out) (order : BufferOrder w.buffer) :
    BufferOrder w'.buffer := by
  cases executor <;> cases d <;> dsimp only [closeWorld, standaloneWorld, updateWorld]
  all_goals first
  | exact order
  | exact BufferOrder.after_put (hp := by assumption) (order.after_erase _) (Or.inr FMap.get_erase_self)
  | exact BufferOrder.after_put (hp := by assumption)
      (order.after_set (by assumption) (Or.inr rfl)) (Or.inl (by assumption))

/-- Every initialized successor buffer is open. -/
theorem initialBuffers_order (init : PipelineInit sig) : BufferOrder (initialBuffers init) := by
  intro i b successor hb hs
  change Finmap.lookup (i + 1) (initialBuffers init) = some successor at hs
  rw [initialBuffers, Finmap.dlookup_list_toFinmap] at hs
  have hm := List.of_mem_dlookup (Option.mem_def.mpr hs)
  obtain ⟨j, hj, he⟩ := List.mem_mapIdx.mp hm
  have hji : j = i + 1 := congrArg Sigma.fst he
  subst j
  have hv : (⟨i + 1, if i + 1 = 0 then init.input else Chunk.emptyOpen⟩ :
      Sigma (fun _ : Nat => Chunk)).2 = successor := by
    exact congrArg Sigma.snd he
  simpa [Chunk.emptyOpen] using congrArg Chunk.flag hv.symm

/-- Initialization and slot-zero delivery preserve successor openness. -/
theorem SelectionDiscipline.bufferOrder {trace : Trace m h executor prog}
    {before selected : World sig} {selection : Selection sig}
    (hd : SelectionDiscipline trace before selection selected)
    (delivery : InputDelivery before selection selected)
    (order : BufferOrder before.buffer) : BufferOrder selected.buffer := by
  rcases hd with ⟨_, _, _, hi, _⟩
  cases hs : selection.init with
  | some init =>
      simp only [hs] at hi
      rw [hi.2.2.2.1]
      exact initialBuffers_order init
  | none =>
      simp only [InputDelivery, hs] at delivery
      cases hd : selection.delivery with
      | none =>
          simp only [hd] at delivery
          simpa [delivery] using order
      | some chunk =>
          simp only [hd] at delivery
          obtain ⟨s, hp, he⟩ := delivery
          rw [he]
          exact order.after_set hp (Or.inl rfl)

/-- Every operational prefix has open immediate successors when present. -/
theorem Operational.bufferOrder {start : World sig}
    {pre : Prefix m h executor prog start} (hop : Operational pre)
    (host : HostWellFormed m h) : BufferOrder pre.final.buffer := by
  apply hop.trace_induction (fun _ w => BufferOrder w.buffer)
  · intro i b successor hb hs
    simp [pre.initial.1, FMap.get] at hb
  · intro earlier hearlier order d he
    have hd := host.selectionDiscipline executor prog start earlier hearlier
      d.selection d.selected (by simpa [he] using d.host)
    have delivery := host.inputDelivery executor prog start earlier hearlier
      d.selection d.selected (by simpa [he] using d.host)
    exact d.probe.bufferOrder (hd.bufferOrder delivery order)

/-- Probe rules never create a sandbox at an absent slot. -/
theorem ProbeDerivation.sandbox_domain_subset {w w' : World sig} {head : Head sig}
    {out : Option Chunk} (d : ProbeDerivation m executor w head w' out) :
    FMap.dom w'.sandbox ⊆ FMap.dom w.sandbox := by
  cases executor <;> cases d <;> dsimp only [closeWorld, standaloneWorld, updateWorld]
  case incr.pipelineOpen p i sb taken remaining r buffers hb hs hi ho hc hstatus hf hp =>
    rw [FMap.dom_set_of_get w.sandbox i _ ⟨sb, hs⟩]
  all_goals first
  | exact Set.Subset.rfl
  | (rw [FMap.dom_erase]; exact fun _ hi => hi.1)

/-- Before any initialization, every operational prefix has no live sandbox. -/
theorem Operational.no_pipeline_empty {start : World sig}
    {pre : Prefix m h executor prog start} (hop : Operational pre)
    (host : HostWellFormed m h) :
    latestPipeline pre.trace = none → FMap.dom pre.final.sandbox = ∅ := by
  apply hop.trace_induction (fun trace w => latestPipeline trace = none → FMap.dom w.sandbox = ∅)
  · intro _
    simp [pre.initial.2.1]
  · intro earlier hearlier previous d he latest
    rw [latestPipeline_snoc] at latest
    have hd := host.selectionDiscipline executor prog start earlier hearlier
      d.selection d.selected (by simpa [he] using d.host)
    rcases hd with ⟨_, _, _, hi, _⟩
    cases hs : d.selection.init with
    | some init => simp [selectedPipeline, hs] at latest
    | none =>
        simp only [selectedPipeline, hs] at latest
        simp only [hs] at hi
        apply Set.eq_empty_of_subset_empty
        have hempty : FMap.dom d.selected.sandbox = ∅ := by
          rw [hi.1]
          exact previous latest
        simpa [hempty] using d.probe.sandbox_domain_subset

/-- An initialized sandbox has exactly the entry filesystem and empty fields. -/
theorem initialSandboxes_get_eq (init : PipelineInit sig) (fs : FS sig)
    {i : Nat} {sb : Sandbox sig}
    (hs : FMap.get (initialSandboxes init fs) i = some sb) : sb = Sandbox.initial fs := by
  change Finmap.lookup i (initialSandboxes init fs) = some sb at hs
  rw [initialSandboxes, Finmap.dlookup_list_toFinmap] at hs
  have hm := List.of_mem_dlookup (Option.mem_def.mpr hs)
  obtain ⟨j, hj, he⟩ := List.mem_mapIdx.mp hm
  exact (congrArg Sigma.snd he).symm

/-- All present sandboxes retain their initialized accumulated fields. -/
def InitialSandboxFields (w : World sig) : Prop :=
  ∀ i sb, FMap.get w.sandbox i = some sb → sb = Sandbox.initial sb.base

/-- H1 preserves initialized fields when no probe accumulation occurs. -/
theorem InitialSandboxFields.selection {trace : Trace m h executor prog}
    {before selected : World sig} {selection : Selection sig}
    (fields : InitialSandboxFields before)
    (hd : SelectionDiscipline trace before selection selected) : InitialSandboxFields selected := by
  intro i sb hs
  rcases hd with ⟨_, _, _, hi, _⟩
  cases hp : selection.init with
  | none =>
      simp only [hp] at hi
      exact fields i sb (by simpa [hi.1] using hs)
  | some init =>
      simp only [hp] at hi
      rw [hi.2.2.2.2] at hs
      have he := initialSandboxes_get_eq init before.fs hs
      subst sb
      rfl

/-- Vanilla rules retain every surviving sandbox's initialized fields. -/
theorem InitialSandboxFields.vanilla {w w' : World sig} {head : Head sig} {out : Option Chunk}
    (fields : InitialSandboxFields w) (d : VanillaDerivation m w head w' out) :
    InitialSandboxFields w' := by
  cases d with
  | openStep => exact fields
  | standalone => exact fields
  | closeStep p j s r es buffers returned hb hc hstatus hf hp =>
      intro i sb hs
      change FMap.get (w.sandbox ∖ j) i = some sb at hs
      by_cases hi : i = j
      · subst i
        rw [FMap.get_erase_self] at hs
        contradiction
      · rw [FMap.get_erase_of_ne hi] at hs
        exact fields i sb hs

/-- Every vanilla prefix retains initialized fields in all surviving sandboxes. -/
theorem Operational.vanilla_initial_fields {start : World sig}
    {pre : Prefix m h .vanilla prog start} (hop : Operational pre)
    (host : HostWellFormed m h) : InitialSandboxFields pre.final := by
  apply hop.trace_induction (fun _ w => InitialSandboxFields w)
  · intro i sb hs
    simp [pre.initial.2.1, FMap.get] at hs
  · intro earlier hearlier fields d he
    have hd := host.selectionDiscipline .vanilla prog start earlier hearlier
      d.selection d.selected (by simpa [he] using d.host)
    exact (fields.selection hd).vanilla d.probe

end

end Incr.Incr
