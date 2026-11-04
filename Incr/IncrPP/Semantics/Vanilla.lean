import Incr.IncrPP.Semantics.Common

/-!
# Vanilla-live raw derivations

Appendix E uses the three vanilla-execution rules (`def:paper-vanilla`) with the
vanilla-live executor label.
Each call reads the current filesystem. Open steps retain slot entries,
closes remove them, and the cache never changes. Freshness and consistent
records are ambient execution conditions, not raw denotation premises.
-/

namespace Incr.IncrPP

variable {sig : Signature}

/-- The three raw vanilla-live branches, with their result witnesses retained. -/
inductive VanillaDerivation (m : CommandModel sig) :
    World sig → Head sig → World sig → Option Chunk → Type where
  | openStep (w : World sig) (p : sig.Probe) (i : Nat) (s' s'' : Bytes)
      (r : Result sig) (buffer' : FMap Nat Chunk) (out : Option Chunk)
      (hbuffer : FMap.get w.buffer i = some ⟨s' ++ s'', .open⟩)
      (hcall : m.denotes p ⟨s', .open⟩ w.fs w.env r)
      (hstatus : r.status = none) (hflag : r.output.flag = .open)
      (hput : put (w.buffer[i ↦ ⟨s'', .open⟩]) i r.output = some (buffer', out)) :
      VanillaDerivation m w (.pipeline p i)
        { w with fs := applyPatch w.fs r.patch, buffer := buffer' } out
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

/-- The existential raw vanilla-live probe judgment. -/
def VanillaStep (m : CommandModel sig) (w : World sig) (head : Head sig)
    (next : World sig) (out : Option Chunk) : Prop :=
  Nonempty (VanillaDerivation m w head next out)

end IncrPP
end Incr
