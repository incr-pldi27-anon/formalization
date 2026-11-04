import Incr.Incr.Bisimulation.Observations
import Incr.Incr.Main.Statements

/-! # From the appendix relation to main Theorem 4.3's observations -/

open Incr
namespace Incr.Incr
noncomputable section
variable {sig : Signature} {m : CommandModel sig} {h : Host sig}
  {prog : sig.Prog} {start : World sig}

private theorem main_put_unique {bl br al ar : FMap Nat Chunk} {i : Nat}
    {left right : Chunk} {out : Option Chunk}
    (before : FMap.get bl (i + 1) = FMap.get br (i + 1))
    (after : al = ar)
    (hl : put bl i left = some (al, out))
    (hr : put br i right = some (ar, out)) : left = right := by
  subst ar
  unfold put at hl hr
  rw [← before] at hr
  cases hn : FMap.get bl (i + 1) with
  | none =>
    simp only [hn, Option.some.injEq, Prod.mk.injEq] at hl hr
    exact Option.some.inj (hl.2.trans hr.2.symm)
  | some next =>
    rcases next with ⟨bytes, flag⟩
    cases flag with
    | eof => simp only [hn, reduceCtorEq] at hl
    | «open» =>
      simp only [hn, Option.some.injEq, Prod.mk.injEq] at hl hr
      have same := congrArg (fun b => FMap.get b (i + 1)) (hl.1.trans hr.1.symm)
      simp only [FMap.get_set_self, Option.some.injEq, Chunk.mk.injEq,
        List.append_cancel_left_eq] at same
      cases left
      cases right
      simp_all only

private theorem main_routing_next {executor : Executor} {w w' : World sig}
    {p : sig.Probe} {i : Nat} {out : Option Chunk}
    (d : ProbeDerivation m executor w (.pipeline p i) w' out) :
    ∃ buffers, ProbeDerivation.routingBuffers d = some buffers ∧
      FMap.get buffers (i + 1) = FMap.get w.buffer (i + 1) ∧
      put buffers i (ProbeDerivation.produced d) = some (w'.buffer, out) := by
  obtain ⟨buffers, hb, hp⟩ := d.routingBuffers_pipeline p i rfl
  refine ⟨buffers, hb, ?_, hp⟩
  cases executor <;> cases d <;>
    simp only [ProbeDerivation.routingBuffers, Option.some.injEq] at hb <;>
    subst buffers <;>
    first | exact FMap.get_set_other (by omega) | exact FMap.get_erase_of_ne (by omega)

private theorem main_standalone_produced {executor : Executor} {w w' : World sig}
    {p : sig.Probe} {out : Option Chunk}
    (d : ProbeDerivation m executor w (.standalone p) w' out) :
    out = some (ProbeDerivation.produced d) := by
  cases executor <;> cases d <;> rfl

private theorem main_probe_produced {wl wr al ar : World sig} {head : Head sig}
    {ol or : Option Chunk} (dl : ProbeDerivation m .incr wl head al ol)
    (dr : ProbeDerivation m .vanilla wr head ar or)
    (selected : ControlAgree wl wr) (after : ControlAgree al ar) (returned : ol = or) :
    ProbeDerivation.produced dl = ProbeDerivation.produced dr := by
  cases head with
  | standalone p =>
    exact Option.some.inj ((main_standalone_produced dl).symm.trans
      (returned.trans (main_standalone_produced dr)))
  | pipeline p i =>
    obtain ⟨bl, _, hbl, hl⟩ := main_routing_next dl
    obtain ⟨br, _, hbr, hr⟩ := main_routing_next dr
    have hr' := hr.trans (congrArg (fun o => some (ar.buffer, o)) returned.symm)
    exact main_put_unique (hbl.trans ((congrArg (fun b => FMap.get b (i + 1))
      selected.2.2.2.1).trans hbr.symm)) after.2.2.2.1 hl hr'

theorem PaperStepsMatch.produced {incr : StepDerivation m h .incr prog}
    {vanilla : StepDerivation m h .vanilla prog} (matched : PaperStepsMatch incr vanilla) :
    ProbeDerivation.produced incr.probe = ProbeDerivation.produced vanilla.probe := by
  rcases incr with ⟨bi, si, wi, ai, oi, hosti, di⟩
  rcases vanilla with ⟨bv, sv, wv, av, ov, hostv, dv⟩
  obtain ⟨returned, selected, after, head, _⟩ := matched
  dsimp only at head selected after returned ⊢
  cases si with
  | mk hi ii =>
    cases sv with
    | mk hv iv =>
      dsimp only at head
      cases head
      exact main_probe_produced di dv selected after returned

private theorem main_connected_steps
    {left : Trace m h .incr prog} {right : Trace m h .vanilla prog}
    (matched : List.Forall₂ PaperStepsMatch left right)
    {wl wr fl fr : World sig} (cl : Connected wl left fl) (cr : Connected wr right fr)
    (before : wl.buffer = wr.buffer) : List.Forall₂ MainStepsMatch left right := by
  induction matched generalizing wl wr with
  | nil => exact .nil
  | @cons dl dr left right step rest ih =>
    cases cl
    cases cr
    exact .cons ⟨step.2.2.2.1, step.2.1.2.2.1, step.hostInput before,
      step.inputs, step.produced, step.1⟩
      (ih (by assumption) (by assumption) step.2.2.1.2.2.2.1)

theorem main_bisimulation_of_strong_bisimulation (witnesses : WitnessMap sig)
    (strong : StrongBisimulation (m := m) (h := h) (prog := prog) (start := start) witnesses) :
    MainBisimulation (m := m) (h := h) (prog := prog) (start := start) witnesses := by
  refine ⟨fun incr vanilla => BisimRelated witnesses incr.val vanilla.val, ?_⟩
  constructor
  · intro incr incr' vanilla label related edge
    obtain ⟨vanilla', edge', related'⟩ := strong.1 incr.val incr'.val vanilla.val label related edge
    exact ⟨⟨vanilla', related'.vanillaAdmissible⟩, edge', related'⟩
  · intro vanilla vanilla' incr label related edge
    obtain ⟨incr', edge', related'⟩ := strong.2.1 vanilla.val vanilla'.val incr.val label related edge
    exact ⟨⟨incr', related'.incrAdmissible⟩, edge', related'⟩
  · intro hi
    have related := strong.2.2.1 hi
    exact ⟨related.incrAdmissible, related.vanillaAdmissible, related⟩
  · intro incr vanilla related
    exact related.equalLength
  · intro incr vanilla related
    exact main_connected_steps related.steps incr.val.connected vanilla.val.connected rfl
  · intro incr vanilla related
    exact (strong.2.2.2 incr.val vanilla.val related).1
  · intro incr vanilla related
    exact (strong.2.2.2 incr.val vanilla.val related).2

end
end Incr.Incr
