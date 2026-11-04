import Incr.IncrPP.Semantics.Execution

/-!
# Connected and operational prefix induction

These structural lemmas split actual connected traces. They do not assume
termination, exit ordering, cache witnesses, or a future host selection.
-/

namespace Incr.IncrPP

variable {sig : Signature} {m : CommandModel sig} {h : Host sig}
  {executor : Executor} {prog : sig.Prog}

/-- Connected concatenation has an actual intermediate world. -/
theorem Connected.append_iff (left right : Trace m h executor prog) (start final : World sig) :
    Connected start (left ++ right) final ↔
      ∃ middle, Connected start left middle ∧ Connected middle right final := by
  induction left generalizing start with
  | nil =>
    constructor
    · intro connected
      exact ⟨start, .nil start, connected⟩
    · rintro ⟨middle, connected, tail⟩
      cases connected
      exact tail
  | cons d rest ih =>
    constructor
    · intro connected
      cases connected with
      | cons _ _ _ tail =>
        obtain ⟨middle, headConnected, tailConnected⟩ := (ih d.after).mp tail
        exact ⟨middle, .cons d rest middle headConnected, tailConnected⟩
    · rintro ⟨middle, connected, tailConnected⟩
      cases connected with
      | cons _ _ _ headConnected =>
        exact .cons d (rest ++ right) final ((ih d.after).mpr ⟨middle, headConnected, tailConnected⟩)

/-- An empty connected trace retains the initial endpoint. -/
theorem Connected.nil_iff (start final : World sig) :
    Connected (m := m) (h := h) (executor := executor) (prog := prog) start [] final ↔
      final = start := by
  constructor
  · intro connected
    cases connected
    rfl
  · rintro rfl
    exact .nil _

/-- A final recorded step determines the shorter prefix's actual endpoint. -/
theorem Connected.snoc_iff (trace : Trace m h executor prog)
    (d : StepDerivation m h executor prog) (start final : World sig) :
    Connected start (trace ++ [d]) final ↔ Connected start trace d.before ∧ final = d.after := by
  constructor
  · intro connected
    obtain ⟨middle, headConnected, tailConnected⟩ :=
      (Connected.append_iff trace [d] start final).mp connected
    cases tailConnected with
    | cons _ _ _ tail =>
      exact ⟨headConnected, (Connected.nil_iff _ _).mp tail⟩
  · rintro ⟨headConnected, rfl⟩
    exact (Connected.append_iff trace [d] start d.after).mpr
      ⟨d.before, headConnected, .cons d [] d.after (.nil d.after)⟩

/-- Timestamp and each-prefix consistency obligations restrict to shorter traces. -/
theorem Operational.of_trace_isPrefix {start : World sig}
    {long short : Prefix m h executor prog start}
    (operational : Operational long) (shorter : short.trace.IsPrefix long.trace) : Operational short := by
  have lengthBound := shorter.length_le
  obtain ⟨suffix, joined⟩ := shorter
  constructor
  · intro d member
    apply operational.timestamps d
    rw [← joined]
    exact List.mem_append_left suffix member
  · intro n bound
    have consistent := operational.consistentPrefixes n (Nat.le_trans bound lengthBound)
    simpa only [← joined, List.take_append_of_le_length bound] using consistent

/-- Induction by the last actual step, with the shorter prefix's real endpoint. -/
theorem Prefix.snoc_induction {start : World sig} (P : Prefix m h executor prog start → Prop)
    (base : ∀ pre, pre.trace = [] → P pre)
    (step : ∀ (short pre : Prefix m h executor prog start) (d : StepDerivation m h executor prog),
      pre.trace = short.trace ++ [d] → short.final = d.before → pre.final = d.after → P short → P pre)
    (pre : Prefix m h executor prog start) : P pre := by
  generalize lengthEq : pre.trace.length = n
  induction n using Nat.strong_induction_on generalizing pre with
  | h n ih =>
    rcases List.eq_nil_or_concat pre.trace with empty | ⟨trace, d, traceEq⟩
    · exact base pre empty
    · have snocTrace : pre.trace = trace ++ [d] := by
        simpa only [List.concat_eq_append] using traceEq
      have connected := pre.connected
      rw [snocTrace] at connected
      obtain ⟨headConnected, endpoint⟩ := (Connected.snoc_iff trace d start pre.final).mp connected
      let short : Prefix m h executor prog start := ⟨trace, d.before, pre.initial, headConnected⟩
      have smaller : short.trace.length < n := by
        change trace.length < n
        rw [← lengthEq, snocTrace, List.length_append, List.length_singleton]
        exact Nat.lt_succ_self _
      exact step short pre d snocTrace rfl endpoint (ih _ smaller short rfl)

/-- Right-step induction retains all ambient execution conditions at the shorter prefix. -/
theorem Operational.snoc_induction {start : World sig} (P : Prefix m h executor prog start → Prop)
    (base : ∀ pre, Operational pre → pre.trace = [] → P pre)
    (step : ∀ (short pre : Prefix m h executor prog start) (d : StepDerivation m h executor prog),
      Operational short → Operational pre → pre.trace = short.trace ++ [d] →
      short.final = d.before → pre.final = d.after → P short → P pre)
    (pre : Prefix m h executor prog start) (operational : Operational pre) : P pre := by
  apply Prefix.snoc_induction (fun pre => Operational pre → P pre) ?_ ?_ pre operational
  · intro pre empty operational
    exact base pre operational empty
  · intro short pre d joined before after ih operational
    have shorter : short.trace.IsPrefix pre.trace := ⟨[d], joined.symm⟩
    have shortOperational := operational.of_trace_isPrefix shorter
    exact step short pre d shortOperational operational joined before after (ih shortOperational)

end IncrPP
end Incr
