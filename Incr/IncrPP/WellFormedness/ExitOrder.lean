import Incr.IncrPP.Semantics.Components
import Incr.IncrPP.Preservation.ComponentLists

/-!
# E.2: exit-ordered sharing

First access is defined only on the accessed-path domain. Its existence
and minimum properties follow from the original trace indices.
Actual steps use one-based positions; an open component ends at prefix length.
The program condition covers all operational terminating runs of both modes,
not only runs consistent with chosen cache witnesses.
-/

namespace Incr.IncrPP

noncomputable section

variable {sig : Signature} {m : CommandModel sig} {h : Host sig}
  {executor : Executor} {prog : sig.Prog}

/-- The nonempty domain required by the paper's first-access minimum. -/
theorem accessPosition_exists (trace : Trace m h executor prog) (k : Component) (q : sig.Path)
    (accessed : q ∈ componentAccesses trace k) :
    ∃ position, position ∈ accessPositions trace k q := by
  classical
  have step : ∃ d ∈ componentSteps trace k, q ∈ d.accesses := by
    rcases accessed with ⟨d, member, read | write⟩ | ⟨d, member, patch⟩
    · exact ⟨d, member, Or.inl (Or.inr read)⟩
    · exact ⟨d, member, Or.inr write⟩
    · exact ⟨d, member, Or.inl (Or.inl patch)⟩
  obtain ⟨d, member, path⟩ := step
  obtain ⟨pos, atPos, component⟩ := (mem_componentSteps_iff trace k d).mp member
  exact ⟨paperPosition pos, (mem_accessPositions_iff trace k q _).mpr
    ⟨pos, d, atPos, component, path, rfl⟩⟩

/-- The minimum is not totalized outside the paper's accessed-path domain. -/
def firstAccess (trace : Trace m h executor prog) (k : Component) (q : sig.Path)
    (accessed : q ∈ componentAccesses trace k) : Nat :=
  Nat.find (accessPosition_exists trace k q accessed)

/-- The minimum has an actual position and is bounded by the recorded prefix. -/
theorem firstAccess_spec (trace : Trace m h executor prog) (k : Component) (q : sig.Path)
    (accessed : q ∈ componentAccesses trace k) :
    firstAccess trace k q accessed ∈ accessPositions trace k q ∧
      0 < firstAccess trace k q accessed ∧ firstAccess trace k q accessed ≤ trace.length ∧
      ∀ position ∈ accessPositions trace k q, firstAccess trace k q accessed ≤ position := by
  classical
  have member : firstAccess trace k q accessed ∈ accessPositions trace k q :=
    Nat.find_spec (accessPosition_exists trace k q accessed)
  have bounds : ∀ position ∈ accessPositions trace k q, 0 < position ∧ position ≤ trace.length := by
    intro position occurrence
    obtain ⟨pos, d, atPos, _, _, rfl⟩ := (mem_accessPositions_iff trace k q position).mp occurrence
    have bound := (List.getElem?_eq_some_iff.mp atPos).choose
    exact ⟨Nat.zero_lt_succ pos, Nat.succ_le_of_lt bound⟩
  refine ⟨member, (bounds _ member).1, (bounds _ member).2, ?_⟩
  intro position occurrence
  exact Nat.find_min' (accessPosition_exists trace k q accessed) occurrence

/-- Use the closing transition, or prefix length for a component that is still open.
The live host discipline will establish uniqueness of a closing position. -/
def lastPosition (trace : Trace m h executor prog) (k : Component) : Nat :=
  (closingPositions trace k).head?.getD trace.length

/-- E.2: ordered distinct pairs from the same initialized pipeline. -/
def ExitOrdered (trace : Trace m h executor prog) : Prop :=
  ∀ entry i j,
    .pipeline entry i ∈ componentDomain trace →
    .pipeline entry j ∈ componentDomain trace → i ≠ j →
    ∀ q (shared : q ∈ componentWrites trace (.pipeline entry i) ∩
        componentAccesses trace (.pipeline entry j)),
      lastPosition trace (.pipeline entry i) <
          firstAccess trace (.pipeline entry j) q shared.2 ∨
        lastPosition trace (.pipeline entry j) <
          firstAccess trace (.pipeline entry i) q (Or.inr shared.1)

/-- E.2: no termination or initial-cache-admission assumption is added to programs. -/
def WellFormedProgram (m : CommandModel sig) (h : Host sig) (prog : sig.Prog)
    (start : World sig) : Prop :=
  ∀ executor (run : Run m h executor prog start),
    Operational run.toPrefix → ExitOrdered run.trace

end
end IncrPP
end Incr
