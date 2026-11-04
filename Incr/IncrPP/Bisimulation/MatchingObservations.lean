import Incr.IncrPP.Bisimulation.Statements
import Incr.IncrPP.Preservation.SlotEffects

/-!
# Observations of matched live and vanilla derivations

Consumed input is determined by the selected and resulting source buffer,
not by host annotation identity. Returned and routed output stay separate.
-/

namespace Incr.IncrPP

noncomputable section

variable {sig : Signature} {m : CommandModel sig} {h : Host sig} {prog : sig.Prog} {start : World sig}

/-- Routing cannot alter the source slot. -/
theorem put_source_lookup {buffers buffers' : FMap Nat Chunk} {i : Nat}
    {output : Chunk} {returned : Option Chunk}
    (routed : put buffers i output = some (buffers', returned)) :
    FMap.get buffers' i = FMap.get buffers i := by
  unfold put at routed
  split at routed
  · cases routed
    rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at routed
    obtain ⟨rfl, rfl⟩ := routed
    exact FMap.get_set_other (by omega)
  · contradiction

/-- The selected and resulting source chunks determine the consumed chunk. -/
def ConsumedFrom (source after : Option Chunk) (input : Chunk) : Prop :=
  (∃ taken remaining : Bytes, source = some ⟨taken ++ remaining, .open⟩ ∧
    after = some ⟨remaining, .open⟩ ∧ input = ⟨taken, .open⟩) ∨
  (∃ bytes : Bytes, source = some ⟨bytes, .eof⟩ ∧ input = ⟨bytes, .eof⟩)

/-- A source and resulting buffer determine a unique consumed chunk. -/
theorem ConsumedFrom.unique {source after : Option Chunk} {left right : Chunk}
    (hl : ConsumedFrom source after left) (hr : ConsumedFrom source after right) : left = right := by
  rcases hl with ⟨taken, remaining, hs, ha, rfl⟩ | ⟨bytes, hs, rfl⟩ <;>
    rcases hr with ⟨taken', remaining', hs', ha', rfl⟩ | ⟨bytes', hs', rfl⟩ <;>
    simp_all [Chunk.mk.injEq]

/-- Every raw pipeline rule consumes the chunk determined by its source buffer effects. -/
theorem ProbeDerivation.pipeline_consumed {executor : Executor}
    {w w' : World sig} {p : sig.Probe} {i : Nat} {out : Option Chunk}
    (d : ProbeDerivation m executor w (.pipeline p i) w' out) :
    ConsumedFrom (FMap.get w.buffer i) (FMap.get w'.buffer i) (ProbeDerivation.input d) := by
  cases executor <;> cases d <;>
    simp only [ProbeDerivation.input, LiveDerivation.input, VanillaDerivation.input,
      closeWorld] <;>
    first
    | (rename_i hp
       have hz := put_source_lookup hp
       simp only [FMap.get_set_self] at hz
       left
       refine ⟨_, _, ?_, hz, rfl⟩
       assumption)
    | (right; exact ⟨_, by assumption, rfl⟩)

/-- A standalone rule consumes its complete selected standard input. -/
theorem ProbeDerivation.standalone_consumed {executor : Executor}
    {w w' : World sig} {p : sig.Probe} {out : Option Chunk}
    (d : ProbeDerivation m executor w (.standalone p) w' out) :
    ProbeDerivation.input d = w.stdin := by
  cases executor <;> cases d <;>
    simp_all [ProbeDerivation.input, LiveDerivation.input, VanillaDerivation.input]

/-- Equal selected and resulting controls force equal raw consumed input. -/
theorem matched_probe_inputs {wl wr al ar : World sig} {head : Head sig}
    {ol or : Option Chunk} (dl : ProbeDerivation m .live wl head al ol)
    (dr : ProbeDerivation m .vanilla wr head ar or)
    (selected : ControlAgree wl wr) (after : ControlAgree al ar) :
    ProbeDerivation.input dl = ProbeDerivation.input dr := by
  cases head with
  | standalone p =>
    exact (ProbeDerivation.standalone_consumed dl).trans
      (selected.2.2.2.2.trans (ProbeDerivation.standalone_consumed dr).symm)
  | pipeline p i =>
    have left := ProbeDerivation.pipeline_consumed dl
    have right := ProbeDerivation.pipeline_consumed dr
    rw [← selected.2.2.2.1, ← after.2.2.2.1] at right
    exact left.unique right

/-- Matched retained steps have equal consumed chunks. -/
theorem MatchingProbeSteps.inputs {live : StepDerivation m h .live prog}
    {vanilla : StepDerivation m h .vanilla prog} (matched : MatchingProbeSteps live vanilla) :
    ProbeDerivation.input live.probe = ProbeDerivation.input vanilla.probe := by
  rcases live with ⟨bl, sl, wl, al, ol, hostl, dl⟩
  rcases vanilla with ⟨br, sr, wr, ar, or, hostr, dr⟩
  obtain ⟨head, _, selected, after, _⟩ := matched
  dsimp only at head selected after ⊢
  cases sl with
  | mk hl il dlv =>
    cases sr with
    | mk hr ir drv =>
      dsimp only at head
      cases head
      exact matched_probe_inputs dl dr selected after

/-- External input observations depend on actual before and selected world effects. -/
theorem MatchingProbeSteps.hostInput {live : StepDerivation m h .live prog}
    {vanilla : StepDerivation m h .vanilla prog} (matched : MatchingProbeSteps live vanilla)
    (before : live.before.buffer = vanilla.before.buffer) : live.hostInput = vanilla.hostInput := by
  obtain ⟨head, _, selected, _, init⟩ := matched
  unfold StepDerivation.hostInput
  rw [head]
  cases vanilla.selection.head with
  | standalone p => rw [selected.2.2.2.2]
  | pipeline p i =>
    have buffers := selected.2.2.2.1
    cases hi : live.selection.init <;> cases hv : vanilla.selection.init <;>
      simp_all

/-- Matched connected traces agree on schedules, environments, supplied input, and consumed input. -/
theorem matching_connected_observations
    {left : Trace m h .live prog} {right : Trace m h .vanilla prog}
    (matched : List.Forall₂ MatchingProbeSteps left right)
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
    obtain ⟨schedule, environments, supplies, inputs⟩ := ih cl cr step.2.2.2.1.2.2.2.1
    exact ⟨congrArg₂ List.cons step.1 schedule,
      congrArg₂ List.cons step.2.2.1.2.2.1 environments,
      congrArg₂ List.cons (step.hostInput before) supplies,
      congrArg₂ List.cons step.inputs inputs⟩

/-- Matched returned chunks yield exactly equal terminal bytes. -/
theorem matching_terminal {left : Trace m h .live prog} {right : Trace m h .vanilla prog}
    (matched : List.Forall₂ MatchingProbeSteps left right) : terminal left = terminal right := by
  unfold terminal
  induction matched with
  | nil => rfl
  | cons step rest ih =>
    simp only [List.flatMap_cons, step.2.1, ih]

/-- Every related pair has all four schedule and input observations. -/
theorem Correspondence.input_observations {context : PrefixContext m h prog start}
    {live : Prefix m h .live prog start} {vanilla : Prefix m h .vanilla prog start}
    (related : Correspondence context live vanilla) :
    SameProbeSchedule live.trace vanilla.trace ∧ SameEnvironments live.trace vanilla.trace ∧
      SameSuppliedInputs live.trace vanilla.trace :=
  matching_connected_observations related.matchingSteps live.connected vanilla.connected rfl

end
end IncrPP
end Incr
