import Incr.Incr.Bisimulation.Statements
import Incr.Incr.Semantics.Observations

open Incr
namespace Incr.Incr

noncomputable section

variable {sig : Signature} {m : CommandModel sig} {h : Host sig}
  {prog : sig.Prog} {start : World sig}

private theorem put_source {buffers buffers' : FMap Nat Chunk} {i : Nat}
    {output : Chunk} {returned : Option Chunk}
    (hp : put buffers i output = some (buffers', returned)) :
    FMap.get buffers' i = FMap.get buffers i := by
  unfold put at hp
  split at hp
  · cases hp
    rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    exact FMap.get_set_other (by omega)
  · contradiction

private def ConsumedFrom (source after : Option Chunk) (input : Chunk) : Prop :=
  (∃ taken remaining : Bytes, source = some ⟨taken ++ remaining, .open⟩ ∧
    after = some ⟨remaining, .open⟩ ∧ input = ⟨taken, .open⟩) ∨
  (∃ bytes : Bytes, source = some ⟨bytes, .eof⟩ ∧ input = ⟨bytes, .eof⟩)

private theorem ConsumedFrom.unique {source after : Option Chunk} {left right : Chunk}
    (hl : ConsumedFrom source after left) (hr : ConsumedFrom source after right) :
    left = right := by
  rcases hl with ⟨taken, remaining, hs, ha, rfl⟩ | ⟨bytes, hs, rfl⟩ <;>
    rcases hr with ⟨taken', remaining', hs', ha', rfl⟩ | ⟨bytes', hs', rfl⟩ <;>
    simp_all [Chunk.mk.injEq]

private theorem pipeline_consumed {executor : Executor}
    {w w' : World sig} {p : sig.Probe} {i : Nat} {out : Option Chunk}
    (d : ProbeDerivation m executor w (.pipeline p i) w' out) :
    ConsumedFrom (FMap.get w.buffer i) (FMap.get w'.buffer i)
      (ProbeDerivation.input d) := by
  cases executor <;> cases d <;>
    simp only [ProbeDerivation.input, IncrDerivation.input, VanillaDerivation.input,
      closeWorld] <;>
    first
    | (rename_i hp
       have hz := put_source hp
       simp only [FMap.get_set_self] at hz
       left
       refine ⟨_, _, ?_, hz, rfl⟩
       assumption)
    | (right; exact ⟨_, by assumption, rfl⟩)

private theorem standalone_consumed {executor : Executor}
    {w w' : World sig} {p : sig.Probe} {out : Option Chunk}
    (d : ProbeDerivation m executor w (.standalone p) w' out) :
    ProbeDerivation.input d = w.stdin := by
  cases executor <;> cases d <;>
    simp_all [ProbeDerivation.input, IncrDerivation.input, VanillaDerivation.input]

private theorem probe_inputs {wl wr al ar : World sig} {head : Head sig}
    {ol or : Option Chunk} (dl : ProbeDerivation m .incr wl head al ol)
    (dr : ProbeDerivation m .vanilla wr head ar or)
    (selected : ControlAgree wl wr) (after : ControlAgree al ar) :
    ProbeDerivation.input dl = ProbeDerivation.input dr := by
  cases head with
  | standalone p =>
    exact (standalone_consumed dl).trans
      (selected.2.2.2.2.trans (standalone_consumed dr).symm)
  | pipeline p i =>
    have hi := pipeline_consumed dl
    have hv := pipeline_consumed dr
    rw [← selected.2.2.2.1, ← after.2.2.2.1] at hv
    exact hi.unique hv

theorem PaperStepsMatch.inputs {incr : StepDerivation m h .incr prog}
    {vanilla : StepDerivation m h .vanilla prog} (matched : PaperStepsMatch incr vanilla) :
    ProbeDerivation.input incr.probe = ProbeDerivation.input vanilla.probe := by
  rcases incr with ⟨bi, si, wi, ai, oi, hosti, di⟩
  rcases vanilla with ⟨bv, sv, wv, av, ov, hostv, dv⟩
  obtain ⟨_, selected, after, head, _⟩ := matched
  dsimp only at head selected after ⊢
  cases si with
  | mk hi ii =>
    cases sv with
    | mk hv iv =>
      dsimp only at head
      cases head
      exact probe_inputs di dv selected after

theorem PaperStepsMatch.hostInput {incr : StepDerivation m h .incr prog}
    {vanilla : StepDerivation m h .vanilla prog} (matched : PaperStepsMatch incr vanilla)
    (before : incr.before.buffer = vanilla.before.buffer) :
    incr.hostInput = vanilla.hostInput := by
  obtain ⟨_, selected, _, head, init⟩ := matched
  unfold StepDerivation.hostInput
  rw [head]
  cases vanilla.selection.head with
  | standalone p => rw [selected.2.2.2.2]
  | pipeline p i =>
    have buffers := selected.2.2.2.1
    cases hi : incr.selection.init <;> cases hv : vanilla.selection.init <;>
      simp_all

private theorem connected_observations
    {left : Trace m h .incr prog} {right : Trace m h .vanilla prog}
    (matched : List.Forall₂ PaperStepsMatch left right)
    {wl wr fl fr : World sig}
    (cl : Connected wl left fl) (cr : Connected wr right fr)
    (before : wl.buffer = wr.buffer) :
    SameProbeSchedule left right ∧ SameEnvironments left right ∧ SameSuppliedInputs left right := by
  induction matched generalizing wl wr with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | @cons dl dr left right step rest ih =>
    cases cl
    cases cr
    rename_i cl cr
    obtain ⟨schedule, environments, supplies, inputs⟩ :=
      ih cl cr step.2.2.1.2.2.2.1
    exact ⟨congrArg₂ List.cons step.2.2.2.1 schedule,
      congrArg₂ List.cons step.2.1.2.2.1 environments,
      congrArg₂ List.cons (step.hostInput before) supplies,
      congrArg₂ List.cons step.inputs inputs⟩

theorem BisimRelated.observations {witnesses}
    {incr : Prefix m h .incr prog start} {vanilla : Prefix m h .vanilla prog start}
    (related : BisimRelated witnesses incr vanilla) :
    SameProbeSchedule incr.trace vanilla.trace ∧
      SameEnvironments incr.trace vanilla.trace ∧
      SameSuppliedInputs incr.trace vanilla.trace :=
  connected_observations related.steps incr.connected vanilla.connected rfl

theorem BisimRelated.terminal {witnesses}
    {incr : Prefix m h .incr prog start} {vanilla : Prefix m h .vanilla prog start}
    (related : BisimRelated witnesses incr vanilla) :
    terminal incr.trace = terminal vanilla.trace := by
  have steps := related.steps
  generalize hl : incr.trace = left at steps ⊢
  generalize hr : vanilla.trace = right at steps ⊢
  clear hl hr
  unfold Incr.Incr.terminal
  induction steps with
  | nil => rfl
  | cons matched rest ih =>
    simp only [List.flatMap_cons, matched.1, ih]

end
end Incr.Incr
