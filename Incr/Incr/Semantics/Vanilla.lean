import Incr.Incr.Semantics.Common

/-!
# Recorded vanilla probe derivations (`def:paper-vanilla`, vanilla execution)

The constructors retain command-call witnesses as data. Their indices match
`ω ⊢ᵥ p → ⟨ω', outs⟩`. The accessors inspect those witnesses directly.
The public proposition `VanillaStep` asserts that a derivation exists.

These are raw rules: the call premise is the command denotation alone.
Execution admissibility separately requires fresh calls and consistent
records. The old rules and traces are not imported.
-/

open Incr
namespace Incr.Incr

variable {sig : Signature}

/-- The three vanilla probe rules, with their witnesses retained as data. -/
inductive VanillaDerivation (m : CommandModel sig) :
    World sig → Head sig → World sig → Option Chunk → Type where
  | openStep (w : World sig) (p : sig.Probe) (i : Nat) (s' s'' : Bytes)
      (r : Result sig) (buffer' : FMap Nat Chunk) (out : Option Chunk)
      (hbuffer : FMap.get w.buffer i = some ⟨s' ++ s'', .open⟩)
      (hcall : m.denotes p ⟨s', .open⟩ w.fs w.env r)
      (hstatus : r.status = none) (hflag : r.output.flag = .open)
      (hput : put (w.buffer[i ↦ ⟨s'', .open⟩]) i r.output = some (buffer', out)) :
      VanillaDerivation m w (.pipeline p i)
        { w with fs := w.fs ⊕ r.patch, buffer := buffer' } out
  | closeStep (w : World sig) (p : sig.Probe) (i : Nat) (s : Bytes)
      (r : Result sig) (x : Nat) (buffer' : FMap Nat Chunk) (out : Option Chunk)
      (hbuffer : FMap.get w.buffer i = some ⟨s, .eof⟩)
      (hcall : m.denotes p ⟨s, .eof⟩ w.fs w.env r)
      (hstatus : r.status = some x) (hflag : r.output.flag = .eof)
      (hput : put (w.buffer ∖ i) i r.output = some (buffer', out)) :
      VanillaDerivation m w (.pipeline p i)
        (closeWorld w i x r.patch buffer') out
  | standalone (w : World sig) (p : sig.Probe) (s : Bytes) (r : Result sig) (x : Nat)
      (hstdin : w.stdin = ⟨s, .eof⟩)
      (hcall : m.denotes p ⟨s, .eof⟩ w.fs w.env r)
      (hstatus : r.status = some x) :
      VanillaDerivation m w (.standalone p)
        (standaloneWorld w x r.patch) (some r.output)

/-- The vanilla rule skeleton. Paper executions additionally satisfy the
shared `Operational` conditions under the model's `DenotationShape` convention. -/
def VanillaStep (m : CommandModel sig) (w : World sig) (head : Head sig)
    (w' : World sig) (out : Option Chunk) : Prop :=
  Nonempty (VanillaDerivation m w head w' out)

namespace VanillaDerivation

variable {m : CommandModel sig}

/-- The chunk consumed in the denotation premise. -/
def input : ∀ {w head w' out}, VanillaDerivation m w head w' out → Chunk
  | _, _, _, _, .openStep _ _ _ s' _ _ _ _ _ _ _ _ _ => ⟨s', .open⟩
  | _, _, _, _, .closeStep _ _ _ s _ _ _ _ _ _ _ _ _ => ⟨s, .eof⟩
  | _, _, _, _, .standalone _ _ s _ _ _ _ _ => ⟨s, .eof⟩

/-- The result selected in the denotation premise. -/
def result : ∀ {w head w' out}, VanillaDerivation m w head w' out → Result sig
  | _, _, _, _, .openStep _ _ _ _ _ r _ _ _ _ _ _ _ => r
  | _, _, _, _, .closeStep _ _ _ _ r _ _ _ _ _ _ _ _ => r
  | _, _, _, _, .standalone _ _ _ r _ _ _ _ => r

/-- Each vanilla call reads the live filesystem of its source world. -/
def callFS {w head w' out} (_d : VanillaDerivation m w head w' out) : Option (FS sig) :=
  some w.fs

end VanillaDerivation

end Incr.Incr
