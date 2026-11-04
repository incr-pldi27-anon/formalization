import Incr.Incr.WellFormedness.Host

/-!
# Internal domain evidence for partial chunk concatenation

Initialization, H1, and the recorded rule effects keep live sandbox chunks
open. These proofs provide typing evidence inside `lem:paper-sandbox` and
`lem:paper-hit-completion` statements.
These proofs do not use numbered preservation results.
-/

open Incr
namespace Incr.Incr

noncomputable section

variable {sig : Signature}

/-- Every present sandbox has open input and output flags. -/
def OpenSandboxes (w : World sig) : Prop :=
  ∀ i sb, FMap.get w.sandbox i = some sb →
    sb.input.flag = .open ∧ sb.output.flag = .open

private theorem open_empty (w : World sig) (he : w.sandbox = ∅) : OpenSandboxes w := by
  intro i sb hs
  simp [he, FMap.get] at hs

private theorem initialSandboxes_value (init : PipelineInit sig) (fs : FS sig)
    {i : Nat} {sb : Sandbox sig}
    (hs : FMap.get (initialSandboxes init fs) i = some sb) : sb = Sandbox.initial fs := by
  change Finmap.lookup i (initialSandboxes init fs) = some sb at hs
  rw [initialSandboxes, Finmap.dlookup_list_toFinmap] at hs
  have hm := List.of_mem_dlookup (β := fun _ : Nat => Sandbox sig)
    (a := i) (b := sb) (l := init.probes.mapIdx fun i _ => ⟨i, Sandbox.initial fs⟩)
    (Option.mem_def.mpr hs)
  have hv : ∀ x ∈ init.probes.mapIdx (fun i _ =>
      (⟨i, Sandbox.initial fs⟩ : Sigma (fun _ : Nat => Sandbox sig))),
      x.2 = Sandbox.initial fs := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_mapIdx.mp hx
    rfl
  exact hv _ hm

/-- H1 preserves open flags, including selections that initialize a pipeline. -/
theorem OpenSandboxes.selection {m : CommandModel sig} {h : Host sig}
    {executor : Executor} {prog : sig.Prog} {trace : Trace m h executor prog}
    {before selected : World sig} {selection : Selection sig}
    (hw : OpenSandboxes before)
    (hd : SelectionDiscipline trace before selection selected) : OpenSandboxes selected := by
  intro i sb hs
  rcases hd with ⟨_, _, _, hinit, _⟩
  cases hi : selection.init with
  | none =>
      simp only [hi] at hinit
      exact hw i sb (by simpa [hinit.1] using hs)
  | some init =>
      simp only [hi] at hinit
      rw [hinit.2.2.2.2] at hs
      have he := initialSandboxes_value init before.fs hs
      subst sb
      exact ⟨rfl, rfl⟩

private theorem open_erase {w : World sig} (hw : OpenSandboxes w)
    (j : Nat) {w' : World sig} (he : w'.sandbox = w.sandbox ∖ j) : OpenSandboxes w' := by
  intro i sb hs
  rw [he] at hs
  by_cases hij : i = j
  · subst i
    rw [FMap.get_erase_self] at hs
    contradiction
  · exact hw i sb (by rwa [FMap.get_erase_of_ne hij] at hs)

/-- The recorded incremental rules preserve open sandbox flags. -/
theorem OpenSandboxes.incr {m : CommandModel sig} {w w' : World sig}
    {head : Head sig} {out : Option Chunk} (hw : OpenSandboxes w)
    (d : IncrDerivation m w head w' out) : OpenSandboxes w' := by
  cases d with
  | pipelineOpen p j sb taken remaining r buffers out hb hs hi ho hc hstatus hf hp =>
      intro i sb' hs'
      dsimp only [updateWorld] at hs'
      by_cases hij : i = j
      · subst i
        rw [FMap.get_set_self] at hs'
        cases Option.some.inj hs'
        exact ⟨rfl, hf⟩
      · exact hw i sb' (by rwa [FMap.get_set_other hij] at hs')
  | uncacheClose => exact open_erase hw _ rfl
  | cacheCloseMiss => exact open_erase hw _ rfl
  | cacheCloseHit => exact open_erase hw _ rfl
  | uncacheStandalone => exact hw
  | cacheStandaloneMiss => exact hw
  | cacheStandaloneHit => exact hw

/-- The recorded vanilla rules preserve open sandbox flags. -/
theorem OpenSandboxes.vanilla {m : CommandModel sig} {w w' : World sig}
    {head : Head sig} {out : Option Chunk} (hw : OpenSandboxes w)
    (d : VanillaDerivation m w head w' out) : OpenSandboxes w' := by
  cases d with
  | openStep => exact hw
  | closeStep => exact open_erase hw _ rfl
  | standalone => exact hw

/-- Connected segments with the same initial world inherit both execution conditions. -/
theorem Operational.of_trace_subset {m : CommandModel sig} {h : Host sig}
    {executor : Executor} {prog : sig.Prog} {start : World sig}
    {pre full : Prefix m h executor prog start} (hop : Operational full)
    (hsub : ∀ d ∈ pre.trace, d ∈ full.trace) : Operational pre := by
  constructor
  · intro d hd
    exact hop.fresh d (hsub d hd)
  · apply TimestampConsistent.mono ?_ hop.timestamps
    intro x hx
    rcases hx with initial | ⟨d, hd, record⟩
    · exact Or.inl initial
    · exact Or.inr ⟨d, hsub d hd, record⟩

private theorem connected_append {m : CommandModel sig} {h : Host sig}
    {executor : Executor} {prog : sig.Prog} {a b c : World sig}
    {xs ys : Trace m h executor prog}
    (hx : Connected a xs b) (hy : Connected b ys c) : Connected a (xs ++ ys) c := by
  induction hx with
  | nil => exact hy
  | cons d rest final ht ih => exact .cons d _ _ (ih hy)

private theorem open_connected {m : CommandModel sig} {h : Host sig}
    {executor : Executor} {prog : sig.Prog} {start w final : World sig}
    {rest : Trace m h executor prog} (hc : Connected w rest final)
    (hh : HostWellFormed m h) (full : Prefix m h executor prog start)
    (hop : Operational full) :
    ∀ (pre : Prefix m h executor prog start), pre.final = w →
      (∀ d ∈ pre.trace, d ∈ full.trace) →
      (∀ d ∈ rest, d ∈ full.trace) → OpenSandboxes pre.final → OpenSandboxes final := by
  induction hc with
  | nil =>
      intro pre he _ _ hw
      simpa [he] using hw
  | cons d rest final ht ih =>
      intro pre he hpre hrest hw
      have hd := hh.selectionDiscipline executor prog start pre
        (hop.of_trace_subset hpre) d.selection d.selected (by simpa [he] using d.host)
      have hs : OpenSandboxes d.selected := hw.selection (by simpa [he] using hd)
      have ha : OpenSandboxes d.after := by
        cases executor with
        | incr => exact hs.incr d.probe
        | vanilla => exact hs.vanilla d.probe
      let next : Prefix m h executor prog start :=
        ⟨pre.trace ++ [d], d.after, pre.initial,
          connected_append pre.connected (by rw [he]; exact .cons d [] d.after (.nil _))⟩
      apply ih next rfl ?_ ?_ ha
      · intro e he
        rcases List.mem_append.mp he with he | he
        · exact hpre e he
        · have hed : e = d := by simpa using he
          subst e
          exact hrest d (by simp)
      · intro e he
        exact hrest e (by simp [he])

/-- Every operational prefix ends with open sandbox input and output flags. -/
theorem Operational.openSandboxes {m : CommandModel sig} {h : Host sig}
    {executor : Executor} {prog : sig.Prog} {start : World sig}
    {pre : Prefix m h executor prog start} (hop : Operational pre)
    (hh : HostWellFormed m h) : OpenSandboxes pre.final := by
  let empty : Prefix m h executor prog start := ⟨[], start, pre.initial, .nil start⟩
  exact open_connected pre.connected hh pre hop empty rfl
    (by simp [empty]) (by simp) (open_empty start pre.initial.2.1)

/-- H1 also gives open flags after any next host selection. -/
theorem Operational.selectedOpenSandboxes {m : CommandModel sig} {h : Host sig}
    {executor : Executor} {prog : sig.Prog} {start : World sig}
    {pre : Prefix m h executor prog start} (hop : Operational pre)
    (hh : HostWellFormed m h) {selection : Selection sig} {selected : World sig}
    (hs : h.select prog pre.final selection selected) : OpenSandboxes selected :=
  (hop.openSandboxes hh).selection
    (hh.selectionDiscipline executor prog start pre hop selection selected hs)

end

end Incr.Incr
