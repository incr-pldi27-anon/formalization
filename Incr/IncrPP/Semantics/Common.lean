import Incr.IncrPP.Semantics.Model

/-!
# Data operations used by live probe rules

These operations use shared state mathematics. They do not import the
sandbox executor. Timestamp conditions belong to the live execution layer.
-/

namespace Incr.IncrPP

noncomputable section

variable {sig : Signature}

/-- The miss policy is exactly store, retain, or erase the selected key. -/
def CacheUpdate (cache : Cache sig) (key : Key sig) (memo : Memo sig)
    (next : Cache sig) : Prop :=
  next = FMap.set cache key memo ∨ next = cache ∨ next = cache ∖ key

/-- Build the complete memo from the slot history and final call. -/
def accumulatedMemo (sb : Sandbox sig) (input : Chunk) (r : Result sig) (x : Nat)
    (hinput : sb.input.flag = .open) (houtput : sb.output.flag = .open)
    (hflag : r.output.flag = .eof) : Memo sig :=
  let accumulated := updateSandbox sb input r hinput houtput
  ⟨x, accumulated.patch, accumulated.reads, accumulated.writes, accumulated.output, hflag⟩

/-- Remove a closing slot and apply only the supplied patch to shared state. -/
def closeWorld (w : World sig) (i : Nat) (x : Nat) (patch : Patch sig)
    (buffers : FMap Nat Chunk) : World sig :=
  { w with
    ec := x
    fs := applyPatch w.fs patch
    buffer := buffers
    sandbox := w.sandbox ∖ i }

/-- Standalone execution consumes complete stdin and applies the supplied patch. -/
def standaloneWorld (w : World sig) (x : Nat) (patch : Patch sig) : World sig :=
  { w with ec := x, fs := applyPatch w.fs patch, stdin := .emptyEOF }

end
end IncrPP
end Incr
