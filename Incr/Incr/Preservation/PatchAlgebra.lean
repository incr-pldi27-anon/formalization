import Incr.Incr.Semantics.Common

/-! # Patch algebra statement (paper `lem:paper-overlay`) -/

open Incr
namespace Incr.Incr

/-- `lem:paper-overlay` (patch algebra): all six patch-algebra claims in the
paper. The frame equation includes absent paths because it compares optional
entries. -/
def PatchAlgebra (sig : Signature) : Prop :=
  (∀ (fs : FS sig) (d₁ d₂ : Patch sig),
    applyPatch (applyPatch fs d₁) d₂ = applyPatch fs (d₁ ⊎ d₂)) ∧
  (∀ fs : FS sig, applyPatch fs ∅ = fs) ∧
  (∀ (fs : FS sig) (d₁ d₂ : Patch sig), Disjoint (FMap.dom d₁) (FMap.dom d₂) →
    applyPatch (applyPatch fs d₁) d₂ = applyPatch (applyPatch fs d₂) d₁) ∧
  (∀ (fs fs' : FS sig) (d d' : Patch sig), FSApprox fs fs' → PatchApprox d d' →
    FSApprox (applyPatch fs d) (applyPatch fs' d')) ∧
  (∀ d₁ d₁' d₂ d₂' : Patch sig, PatchApprox d₁ d₁' → PatchApprox d₂ d₂' →
    PatchApprox (d₁ ⊎ d₂) (d₁' ⊎ d₂')) ∧
  (∀ (fs : FS sig) (d : Patch sig) q, q ∉ FMap.dom d →
    FMap.get (applyPatch fs d) q = FMap.get fs q)

end Incr.Incr
