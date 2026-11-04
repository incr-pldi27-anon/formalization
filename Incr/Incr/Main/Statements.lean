import Incr.Incr.Bisimulation.Statements
import Incr.Incr.Semantics.Observations

/-!
# Main Theorem 4.3: strong bisimulation

This interface states `thm:main-bisimulation` with an existential relation on
admissible prefixes. It does not fix the relation used in the appendix.
-/

open Incr
namespace Incr.Incr

variable {sig : Signature} {m : CommandModel sig} {h : Host sig}
  {prog : sig.Prog} {start : World sig}

/-- A state of either admissible-prefix system, with fixed initial witnesses. -/
abbrev MainAdmissiblePrefix (witnesses : WitnessMap sig) (executor : Executor) :=
  {pre : Prefix m h executor prog start // Admissible witnesses pre}

/-- The six observations at corresponding steps in main Theorem 4.3.
Host input is the state-based paper effect, not the optional delivery annotation. -/
structure MainStepsMatch (incr : StepDerivation m h .incr prog)
    (vanilla : StepDerivation m h .vanilla prog) : Prop where
  probeLabel : incr.selection.head = vanilla.selection.head
  environment : incr.selected.env = vanilla.selected.env
  hostInput : incr.hostInput = vanilla.hostInput
  consumed : ProbeDerivation.input incr.probe = ProbeDerivation.input vanilla.probe
  produced : ProbeDerivation.produced incr.probe = ProbeDerivation.produced vanilla.probe
  returned : incr.out = vanilla.out

/-- The properties of the existential relation in `thm:main-bisimulation`.
Equal length is separate from the six corresponding-step equations.
Final observations exclude timestamps and caches. -/
structure MainBisimulationProperties (witnesses : WitnessMap sig)
    (related : MainAdmissiblePrefix (m := m) (h := h) (prog := prog) (start := start)
        witnesses .incr →
      MainAdmissiblePrefix (m := m) (h := h) (prog := prog) (start := start)
        witnesses .vanilla → Prop) : Prop where
  forward : ∀
    (incr incr' : MainAdmissiblePrefix (m := m) (h := h) (prog := prog) (start := start)
      witnesses .incr)
    (vanilla : MainAdmissiblePrefix (m := m) (h := h) (prog := prog) (start := start)
      witnesses .vanilla) (label : Head sig),
    related incr vanilla → PrefixStep witnesses label incr.val incr'.val →
    ∃ vanilla' : MainAdmissiblePrefix (m := m) (h := h) (prog := prog) (start := start)
        witnesses .vanilla,
      PrefixStep witnesses label vanilla.val vanilla'.val ∧ related incr' vanilla'
  backward : ∀
    (vanilla vanilla' : MainAdmissiblePrefix (m := m) (h := h) (prog := prog) (start := start)
      witnesses .vanilla)
    (incr : MainAdmissiblePrefix (m := m) (h := h) (prog := prog) (start := start)
      witnesses .incr) (label : Head sig),
    related incr vanilla → PrefixStep witnesses label vanilla.val vanilla'.val →
    ∃ incr' : MainAdmissiblePrefix (m := m) (h := h) (prog := prog) (start := start)
        witnesses .incr,
      PrefixStep witnesses label incr.val incr'.val ∧ related incr' vanilla'
  initial : ∀ hi : Initial h prog start,
    ∃ (incrAdmissible : Admissible witnesses (emptyPrefix m h .incr prog start hi))
      (vanillaAdmissible : Admissible witnesses (emptyPrefix m h .vanilla prog start hi)),
      related ⟨emptyPrefix m h .incr prog start hi, incrAdmissible⟩
        ⟨emptyPrefix m h .vanilla prog start hi, vanillaAdmissible⟩
  equalLength : ∀ incr vanilla, related incr vanilla →
    incr.val.trace.length = vanilla.val.trace.length
  steps : ∀ incr vanilla, related incr vanilla →
    List.Forall₂ MainStepsMatch incr.val.trace vanilla.val.trace
  completion : ∀ incr vanilla, related incr vanilla →
    (h.complete prog incr.val.final ↔ h.complete prog vanilla.val.final)
  finalObservations : ∀ incr vanilla, related incr vanilla →
    h.complete prog incr.val.final →
      terminal incr.val.trace = terminal vanilla.val.trace ∧
      incr.val.final.ec = vanilla.val.final.ec ∧
      FSApprox incr.val.final.fs vanilla.val.final.fs

/-- The conclusion of main Theorem 4.3, `thm:main-bisimulation`.
The relation ranges only over the two admissible-prefix systems. -/
def MainBisimulation (witnesses : WitnessMap sig) : Prop :=
  ∃ related : MainAdmissiblePrefix (m := m) (h := h) (prog := prog) (start := start)
        witnesses .incr →
      MainAdmissiblePrefix (m := m) (h := h) (prog := prog) (start := start)
        witnesses .vanilla → Prop,
    MainBisimulationProperties witnesses related

end Incr.Incr
