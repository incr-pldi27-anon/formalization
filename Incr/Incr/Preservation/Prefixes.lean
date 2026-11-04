import Incr.Incr.Preservation.Cache
import Incr.Incr.Preservation.Buffers

/-! # Joint cache and cacheable-prefix preservation -/

open Incr
namespace Incr.Incr.PrefixPreservation

noncomputable section

variable {sig : Signature} {m : CommandModel sig} {h : Host sig}
  {prog : sig.Prog} {start : World sig}

private theorem connected_snoc {a b : World sig} {xs : Trace m h .incr prog}
    (hc : Connected a xs b) (d : StepDerivation m h .incr prog) (he : b = d.before) :
    Connected a (xs ++ [d]) d.after := by
  induction hc with
  | nil => rw [he]; exact .cons d [] d.after (.nil _)
  | cons e rest final ht ih => exact .cons e _ _ (ih he)

private theorem trace_induction_next {full : Prefix m h .incr prog start}
    (hop : Operational full) (P : Trace m h .incr prog → World sig → Prop)
    (initial : P [] start)
    (step : ∀ (pre : Prefix m h .incr prog start), Operational pre → P pre.trace pre.final →
      ∀ d : StepDerivation m h .incr prog, ∀ he : pre.final = d.before,
      Operational (⟨pre.trace ++ [d], d.after, pre.initial, connected_snoc pre.connected d he⟩ :
        Prefix m h .incr prog start) → P (pre.trace ++ [d]) d.after) :
    P full.trace full.final := by
  suffices aux : ∀ hc : Connected start full.trace full.final,
      Operational (⟨full.trace, full.final, full.initial, hc⟩ : Prefix m h .incr prog start) →
      P full.trace full.final from aux full.connected hop
  apply hop.trace_induction (fun trace w => ∀ hc : Connected start trace w,
    Operational (⟨trace, w, full.initial, hc⟩ : Prefix m h .incr prog start) → P trace w)
  · intro _ _
    exact initial
  · intro pre op ih d he hc nextop
    exact step pre op (ih pre.connected op) d he nextop

private def SelectedPrefixes (trace : Trace m h .incr prog) (sel : Selection sig)
    (w : World sig) : Prop :=
  ∀ i sb k first, FMap.get w.sandbox i = some sb →
    selectedComponent trace sel i = some k → (openHistory trace k).head? = some first →
    Cacheable m first.selection.head.probe →
    m.denotes first.selection.head.probe sb.input sb.base first.selected.env (sandboxResult sb)

private def SelectedEmpty (trace : Trace m h .incr prog) (sel : Selection sig)
    (w : World sig) : Prop :=
  ∀ i sb k, FMap.get w.sandbox i = some sb →
    selectedComponent trace sel i = some k → openHistory trace k = [] →
    sb = Sandbox.initial sb.base

private theorem selection_prefixes {pre : Prefix m h .incr prog start}
    (prefixes : CacheablePrefixes pre.trace pre.final)
    {sel : Selection sig} {w : World sig}
    (hd : SelectionDiscipline pre.trace pre.final sel w) : SelectedPrefixes pre.trace sel w := by
  intro i sb k first hs hl hf hc
  cases hi : sel.init with
  | none =>
    have hh := hd.2.2.2.1
    simp only [hi] at hh
    have hm := hh.1
    exact prefixes i sb k first (by simpa [hm] using hs)
      (by simpa [selectedComponent, selectedPipeline, hi, liveComponent] using hl) hf hc
  | some init =>
    have hk : k = .pipeline pre.trace.length i := by
      simpa [selectedComponent, selectedPipeline, hi] using hl.symm
    subst k
    have hz := componentSteps_future_entry pre.trace (entry := pre.trace.length) i (by omega)
    simp [openHistory, hz] at hf

private theorem selection_empty {pre : Prefix m h .incr prog start}
    (state : SandboxState pre.trace pre.final)
    {sel : Selection sig} {w : World sig}
    (hd : SelectionDiscipline pre.trace pre.final sel w) : SelectedEmpty pre.trace sel w := by
  intro i sb k hs hl hempty
  cases hi : sel.init with
  | none =>
    have hh := hd.2.2.2.1
    simp only [hi] at hh
    have hm := hh.1
    have hs' : FMap.get pre.final.sandbox i = some sb := by simpa [hm] using hs
    obtain ⟨entry, init, d, latest, _, _, _, acc⟩ := state.2.1 i sb hs'
    have hk : k = .pipeline entry i := by
      simpa [selectedComponent, selectedPipeline, hi, latest] using hl.symm
    subst k
    change HistoryAccumulation sb.base (openHistory pre.trace (.pipeline entry i)) sb at acc
    exact CachePrefixes.accumulation_nil (by simpa [hempty] using acc)
  | some init =>
    have hm : w.sandbox = initialSandboxes init pre.final.fs := by
      have hh := hd.2.2.2.1
      simp only [hi] at hh
      exact hh.2.2.2.2
    have he := initialSandboxes_get_eq init pre.final.fs (by simpa [hm] using hs)
    subst sb
    rfl

private theorem selected_slot {trace : Trace m h .incr prog} {sel : Selection sig}
    {i j : Nat} {k : Component}
    (hi : selectedComponent trace sel i = some k)
    (hj : selectedComponent trace sel j = some k) : i = j := by
  unfold selectedComponent at hi hj
  cases hp : selectedPipeline trace sel with
  | none => simp [hp] at hi
  | some pair =>
    simp only [hp, Option.map_some, Option.some.injEq] at hi hj
    have := hi.trans hj.symm
    cases this
    rfl

private theorem selected_present {trace : Trace m h .incr prog}
    {before w : World sig} {sel : Selection sig}
    (hd : SelectionDiscipline trace before sel w) {p : sig.Probe} {i : Nat}
    (hh : sel.head = .pipeline p i) : ∃ k, selectedComponent trace sel i = some k := by
  have ha := hd.2.2.2.2
  rw [hh] at ha
  obtain ⟨_, _, _, probes, hp, _⟩ := ha
  unfold selectedComponent selectedPipeline
  cases hi : sel.init with
  | some init => exact ⟨_, rfl⟩
  | none =>
    cases hl : latestPipeline trace with
    | none => simp [assignedProbes, hi, hl] at hp
    | some pair => exact ⟨_, rfl⟩

private theorem selected_fold (commands : WellFormedCommands m)
    {trace : Trace m h .incr prog} {d : StepDerivation m h .incr prog}
    (prefixes : SelectedPrefixes trace d.selection d.selected)
    (empty : SelectedEmpty trace d.selection d.selected)
    (stable : ComponentEnvironments (trace ++ [d]))
    {p : sig.Probe} {i : Nat} {sb : Sandbox sig} {k : Component}
    (hh : d.selection.head = .pipeline p i)
    (hl : selectedComponent trace d.selection i = some k)
    (hs : FMap.get d.selected.sandbox i = some sb) (hc : Cacheable m p)
    (hi : sb.input.flag = .open) (ho : sb.output.flag = .open)
    {input : Chunk} {result : Result sig}
    (call : m.denotes p input sb.view d.selected.env result) :
    m.denotes p (sb.input ++'hi input) sb.base d.selected.env
      (combineResults (sandboxResult sb) result ho) := by
  cases hf : (openHistory trace k).head? with
  | none =>
    have hz := List.head?_eq_none_iff.mp hf
    have he := empty i sb k hs hl hz
    have call' : m.denotes p input (Sandbox.initial sb.base).view d.selected.env result := by
      simpa only [← he] using call
    convert CachePrefixes.fold_initial call' using 1 <;> simp only [← he]
  | some first =>
    have hat : componentAt (trace ++ [d]) trace.length d = some k := by
      rw [componentAt_snoc_last, hh]
      exact hl
    obtain ⟨hhist, henv⟩ := CachePrefixes.extension_historical_fields stable hf hat
    have hfirst : first.selection.head = .pipeline p i := hhist.symm.trans hh
    have denoted := prefixes i sb k first hs hl hf
      (by simpa only [hfirst, Head.probe] using hc)
    rw [hfirst] at denoted
    rw [henv] at call ⊢
    exact CachePrefixes.fold_progressed commands hc hi ho denoted call

private theorem live_snoc (trace : Trace m h .incr prog)
    (d : StepDerivation m h .incr prog) (i : Nat) :
    liveComponent (trace ++ [d]) i = selectedComponent trace d.selection i := by
  simp only [liveComponent, latestPipeline_snoc, selectedComponent]

private theorem unchanged_prefixes {trace : Trace m h .incr prog}
    {d : StepDerivation m h .incr prog}
    (prefixes : SelectedPrefixes trace d.selection d.selected)
    (maps : ∀ i sb, FMap.get d.after.sandbox i = some sb →
      FMap.get d.selected.sandbox i = some sb)
    (hist : ∀ k, openHistory (trace ++ [d]) k = openHistory trace k) :
    CacheablePrefixes (trace ++ [d]) d.after := by
  intro i sb k first hs hl hf hc
  exact prefixes i sb k first (maps i sb hs) (by simpa only [live_snoc] using hl)
    (by simpa only [hist] using hf) hc

private theorem erased_get {map : FMap Nat (Sandbox sig)} {i j : Nat} {sb : Sandbox sig}
    (hs : FMap.get (map ∖ j) i = some sb) : FMap.get map i = some sb := by
  by_cases hi : i = j
  · subst i
    simp only [FMap.get_erase_self] at hs
    contradiction
  · simpa only [FMap.get_erase_of_ne hi] using hs

private theorem open_update_prefixes (commands : WellFormedCommands m)
    {trace : Trace m h .incr prog} {d : StepDerivation m h .incr prog}
    (prefixes : SelectedPrefixes trace d.selection d.selected)
    (empty : SelectedEmpty trace d.selection d.selected)
    (stable : ComponentEnvironments (trace ++ [d]))
    {p : sig.Probe} {j : Nat} {old : Sandbox sig} {input : Chunk} {result : Result sig}
    (hh : d.selection.head = .pipeline p j)
    (hsold : FMap.get d.selected.sandbox j = some old)
    (hi : old.input.flag = .open) (ho : old.output.flag = .open)
    (hmap : d.after.sandbox = d.selected.sandbox[j ↦ (old.accumulate input result hi ho)])
    (hstatus : result.status = none)
    (call : m.denotes p input old.view d.selected.env result) :
    CacheablePrefixes (trace ++ [d]) d.after := by
  intro i sb k first hs hl hf hc
  have hsel : selectedComponent trace d.selection i = some k := by
    simpa only [live_snoc] using hl
  rw [hmap] at hs
  by_cases hij : i = j
  · subst i
    rw [FMap.get_set_self] at hs
    cases Option.some.inj hs
    have hat : componentAt (trace ++ [d]) trace.length d = some k := by
      rw [componentAt_snoc_last, hh]
      exact hsel
    have hdmem : d ∈ componentSteps (trace ++ [d]) k := by
      rw [componentSteps_snoc]
      simp [hat]
    obtain ⟨hhist, henv⟩ := CachePrefixes.component_environment_uniform stable hdmem
      (CachePrefixes.first_open_mem hf)
    have hfirst : first.selection.head = .pipeline p j := hhist.symm.trans hh
    have hcp : Cacheable m p := by simpa only [hfirst, Head.probe] using hc
    rw [hfirst, ← henv]
    rw [CachePrefixes.accumulated_open_result _ _ _ _ _ hstatus]
    exact selected_fold commands prefixes empty stable hh hsel hsold hcp hi ho call
  · rw [FMap.get_set_other hij] at hs
    have hnot : componentAt (trace ++ [d]) trace.length d ≠ some k := by
      intro hat
      rw [componentAt_snoc_last, hh] at hat
      exact hij (selected_slot hsel hat)
    have hist : openHistory (trace ++ [d]) k = openHistory trace k := by
      simp [openHistory_snoc, hnot]
    exact prefixes i sb k first hs hsel (by simpa only [hist] using hf) hc

private theorem raw_prefixes (commands : WellFormedCommands m)
    {trace : Trace m h .incr prog} (d : StepDerivation m h .incr prog)
    (prefixes : SelectedPrefixes trace d.selection d.selected)
    (empty : SelectedEmpty trace d.selection d.selected)
    (stable : ComponentEnvironments (trace ++ [d])) :
    CacheablePrefixes (trace ++ [d]) d.after := by
  cases d with
  | mk before sel w after out host probe =>
    cases sel with
    | mk head init delivery =>
      cases probe with
      | pipelineOpen p j sb taken remaining r buffers returned hb hs hi ho call hstatus hflag hp =>
        exact open_update_prefixes commands prefixes empty stable rfl hs hi ho rfl hstatus call
      | uncacheClose =>
        apply unchanged_prefixes prefixes
        · intro i sb hs
          exact erased_get hs
        · intro k
          simp [openHistory_snoc, ProbeDerivation.input, IncrDerivation.input]
      | cacheCloseMiss =>
        apply unchanged_prefixes prefixes
        · intro i sb hs
          exact erased_get hs
        · intro k
          simp [openHistory_snoc, ProbeDerivation.input, IncrDerivation.input]
      | cacheCloseHit =>
        apply unchanged_prefixes prefixes
        · intro i sb hs
          exact erased_get hs
        · intro k
          simp [openHistory_snoc, ProbeDerivation.input, IncrDerivation.input]
      | uncacheStandalone =>
        apply unchanged_prefixes prefixes
        · intro i sb hs
          exact hs
        · intro k
          simp [openHistory_snoc, ProbeDerivation.input, IncrDerivation.input]
      | cacheStandaloneMiss =>
        apply unchanged_prefixes prefixes
        · intro i sb hs
          exact hs
        · intro k
          simp [openHistory_snoc, ProbeDerivation.input, IncrDerivation.input]
      | cacheStandaloneHit =>
        apply unchanged_prefixes prefixes
        · intro i sb hs
          exact hs
        · intro k
          simp [openHistory_snoc, ProbeDerivation.input, IncrDerivation.input]

theorem joint_preservation (commands : WellFormedCommands m) (host : HostWellFormed m h)
    (cache : WellFormedCache m start.cache)
    (states : ∀ (earlier : Prefix m h .incr prog start), Operational earlier →
      SandboxState earlier.trace earlier.final)
    (pre : Prefix m h .incr prog start) (operational : Operational pre) :
    WellFormedCache m pre.final.cache ∧ CacheablePrefixes pre.trace pre.final := by
  apply trace_induction_next operational
    (fun trace w => WellFormedCache m w.cache ∧ CacheablePrefixes trace w)
  · refine ⟨cache, ?_⟩
    intro i sb k first hs
    simp [pre.initial.2.1, FMap.get] at hs
  · intro earlier op ih d he nextop
    have hd := host.selectionDiscipline .incr prog start earlier op d.selection d.selected
      (by simpa only [he] using d.host)
    have state := states earlier op
    have prefixes := selection_prefixes ih.2 hd
    have empty := selection_empty state hd
    let next : Prefix m h .incr prog start :=
      ⟨earlier.trace ++ [d], d.after, earlier.initial, connected_snoc earlier.connected d he⟩
    have stable : ComponentEnvironments (earlier.trace ++ [d]) :=
      host.componentEnvironments .incr prog start next nextop
    refine ⟨?_, raw_prefixes commands d prefixes empty stable⟩
    apply CachePrefixes.incr_cache_preservation (w := d.selected)
      (by simpa only [hd.2.2.1] using ih.1) ?_ d.probe
    intro p i sb hh hs hc input result hi ho call
    obtain ⟨k, hl⟩ := selected_present hd hh
    exact selected_fold commands prefixes empty stable hh hl hs hc hi ho call

end
end Incr.Incr.PrefixPreservation


