import Incr.Incr.Preservation.Buffers
import Incr.Incr.Preservation.Cache

/-! # Probe assignments and prefix denotations at host selection -/

open Incr
namespace Incr.Incr

noncomputable section

variable {sig : Signature} {m : CommandModel sig} {h : Host sig}
  {executor : Executor} {prog : sig.Prog} {start : World sig}

/-- Each historical pipeline call uses the probe assigned by its actual entry. -/
theorem hit_history_assignment (pre : Prefix m h executor prog start)
    (operational : Operational pre) (host : HostWellFormed m h) :
    ∀ entry slot d, d ∈ componentSteps pre.trace (.pipeline entry slot) →
      ∃ (p : sig.Probe) (init : PipelineInit sig) (entryStep : StepDerivation m h executor prog),
        (pre.trace)[entry]? = some entryStep ∧ entryStep.selection.init = some init ∧
        d.selection.head = .pipeline p slot ∧ init.probes[slot]? = some p := by
  apply operational.trace_induction (fun trace _ =>
    ∀ entry slot d, d ∈ componentSteps trace (.pipeline entry slot) →
      ∃ (p : sig.Probe) (init : PipelineInit sig) (entryStep : StepDerivation m h executor prog),
        (trace)[entry]? = some entryStep ∧ entryStep.selection.init = some init ∧
        d.selection.head = .pipeline p slot ∧ init.probes[slot]? = some p)
  · intro entry slot d hd
    simp [componentSteps] at hd
  · intro earlier hop ih d he entry slot e hm
    rw [componentSteps_snoc] at hm
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨p, init, entryStep, hat, hi, hh, hp⟩ := ih entry slot e hm
      have hl := (List.getElem?_eq_some_iff.mp hat).1
      exact ⟨p, init, entryStep, by simpa [List.getElem?_append, hl] using hat, hi, hh, hp⟩
    · have hc : componentAt (earlier.trace ++ [d]) earlier.trace.length d =
          some (.pipeline entry slot) := by
        split at hm
        · assumption
        · simp at hm
      have hed : e = d := by
        split at hm <;> simp_all
      subst e
      have hd := host.selectionDiscipline executor prog start earlier hop
        d.selection d.selected (by simpa only [he] using d.host)
      rw [componentAt_snoc_last] at hc
      cases hh : d.selection.head with
      | standalone p => simp [hh] at hc
      | pipeline p j =>
        simp only [hh] at hc
        have hslot : j = slot := by
          cases hs : selectedPipeline earlier.trace d.selection with
          | none => simp [selectedComponent, hs] at hc
          | some pair =>
            have eqs : pair.1 = entry ∧ j = slot := by
              simpa [selectedComponent, hs] using hc
            exact eqs.2
        subst j
        have ha := hd.2.2.2.2
        rw [hh] at ha
        obtain ⟨_, _, _, probes, assigned, probe⟩ := ha
        cases hi : d.selection.init with
        | none =>
          cases hl : latestPipeline earlier.trace with
          | none => simp [assignedProbes, hi, hl] at assigned
          | some pair =>
            obtain ⟨oldEntry, init⟩ := pair
            have hentry : oldEntry = entry := by
              simpa [selectedComponent, selectedPipeline, hi, hl] using hc
            subst oldEntry
            have hp : init.probes[slot]? = some p := by
              have hprobes : init.probes = probes := by
                simpa [assignedProbes, hi, hl] using assigned
              simpa only [hprobes] using probe
            obtain ⟨entryStep, hat, heinit⟩ := latestPipeline_witness earlier.trace hl
            have hlt := (List.getElem?_eq_some_iff.mp hat).1
            exact ⟨p, init, entryStep, by simpa [List.getElem?_append, hlt] using hat,
              heinit, rfl, hp⟩
        | some init =>
          have hentry : earlier.trace.length = entry := by
            simpa [selectedComponent, selectedPipeline, hi] using hc
          have hp : init.probes[slot]? = some p := by
            have hprobes : init.probes = probes := by simpa [assignedProbes, hi] using assigned
            simpa only [hprobes] using probe
          exact ⟨p, init, d, by simp [← hentry], hi, rfl, hp⟩

/-- H1 and O1 put the accumulated prefix in the selected probe's environment. -/
theorem hit_selected_prefix_cases
    {pre : Prefix m h .incr prog start} (operational : Operational pre)
    (host : HostWellFormed m h)
    (state : SandboxState pre.trace pre.final)
    (prefixes : CacheablePrefixes pre.trace pre.final)
    {selection : Selection sig} {selected : World sig}
    (chosen : h.select prog pre.final selection selected)
    {p : sig.Probe} {i : Nat} {sb : Sandbox sig}
    (head : selection.head = .pipeline p i)
    (sandbox : FMap.get selected.sandbox i = some sb)
    (cacheable : Cacheable m p) :
    sb = Sandbox.initial sb.base ∨
      m.denotes p sb.input sb.base selected.env (sandboxResult sb) := by
  have hd := host.selectionDiscipline .incr prog start pre operational selection selected chosen
  cases hi : selection.init with
  | some init =>
    have hs : selected.sandbox = initialSandboxes init pre.final.fs := by
      have hinit := hd.2.2.2.1
      simp only [hi] at hinit
      exact hinit.2.2.2.2
    have initial := initialSandboxes_get_eq init pre.final.fs (by simpa only [hs] using sandbox)
    left
    have baseEq : sb.base = pre.final.fs := congrArg Sandbox.base initial
    simpa only [baseEq] using initial
  | none =>
    have hs : selected.sandbox = pre.final.sandbox := by
      have hinit := hd.2.2.2.1
      simp only [hi] at hinit
      exact hinit.1
    have hsandbox : FMap.get pre.final.sandbox i = some sb := by
      simpa only [hs] using sandbox
    obtain ⟨entry, init, entryStep, latest, atEntry, initEntry, _, accumulation⟩ :=
      state.2.1 i sb hsandbox
    change HistoryAccumulation sb.base (openHistory pre.trace (.pipeline entry i)) sb at accumulation
    cases hf : (openHistory pre.trace (.pipeline entry i)).head? with
    | none =>
      left
      exact accumulation.eq_initial (List.head?_eq_none_iff.mp hf)
    | some first =>
      have live : liveComponent pre.trace i = some (.pipeline entry i) := by
        simp only [liveComponent, latest, Option.map_some]
      obtain ⟨oldProbe, oldInit, oldEntryStep, oldAt, oldInitAt, oldHead, oldAssigned⟩ :=
        hit_history_assignment pre operational host entry i first (CachePrefixes.first_open_mem hf)
      have stepEq : oldEntryStep = entryStep := Option.some.inj (oldAt.symm.trans atEntry)
      have initEq : oldInit = init := Option.some.inj (oldInitAt.symm.trans (stepEq ▸ initEntry))
      have ha := hd.2.2.2.2
      rw [head] at ha
      obtain ⟨_, _, _, probes, assigned, probe⟩ := ha
      have probesEq : init.probes = probes := by
        simpa only [assignedProbes, hi, latest, Option.map_some, Option.some.injEq] using assigned
      have assignedNow : init.probes[i]? = some p := by simpa only [probesEq] using probe
      have probeEq : oldProbe = p := by
        have oldAssigned' : init.probes[i]? = some oldProbe := by simpa only [initEq] using oldAssigned
        exact Option.some.inj (oldAssigned'.symm.trans assignedNow)
      have firstHead : first.selection.head = .pipeline p i := by simpa only [probeEq] using oldHead
      have denoted := prefixes i sb (.pipeline entry i) first hsandbox live hf
        (by simpa only [firstHead, Head.probe] using cacheable)
      have envEq := CachePrefixes.selected_historical_env host operational chosen hi head live hf
      right
      simpa only [firstHead, Head.probe, ← envEq] using denoted

end
end Incr.Incr
