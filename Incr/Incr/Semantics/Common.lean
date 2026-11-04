import Incr.Model.Cache

/-!
# Shared definitions for the independent recorded experiment

Only the shared data and command specification enter this subtree.
No current rule, trace, host contract, or soundness proof is imported.
The raw rules use command denotations. Freshness belongs to the execution
conditions in `Incr.Incr.Semantics.Execution`, not to the transition constructors.
-/

open Incr
namespace Incr.Incr

noncomputable section

variable {sig : Signature}

/-- The two executors compared in the Incr 1.0 experiment. -/
inductive Executor where
  | incr
  | vanilla
  deriving DecidableEq, Repr

/-- The complete memo built at a cacheable pipeline miss. -/
def accumulatedMemo (sb : Sandbox sig) (input : Chunk) (r : Result sig) (x : Nat)
    (hinput : sb.input.flag = .open) (houtput : sb.output.flag = .open)
    (hflag : r.output.flag = .eof) : Memo sig :=
  let accumulated := sb.accumulate input r hinput houtput
  ⟨x, accumulated.patch, accumulated.reads, accumulated.writes, accumulated.output, hflag⟩

/-- A pipeline close applies the complete patch and removes its sandbox. -/
def closeWorld (w : World sig) (i : Nat) (x : Nat) (d : Patch sig)
    (buffers : FMap Nat Chunk) : World sig :=
  { w with
    ec := x
    fs := w.fs ⊕ d
    buffer := buffers
    sandbox := w.sandbox ∖ i }

/-- A standalone call consumes the complete stdin chunk. -/
def standaloneWorld (w : World sig) (x : Nat) (d : Patch sig) : World sig :=
  { w with ec := x, fs := applyPatch w.fs d, stdin := .emptyEOF }

end

end Incr.Incr
