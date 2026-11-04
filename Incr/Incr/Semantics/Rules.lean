import Incr.Incr.Semantics.Vanilla

/-!
# Recorded Incr 1.0 probe derivations (paper `app:incr-rules`, Appendix B.1)

The conclusion contains only the source world, probe, target world, and
output returned to the host. Execution and replay witnesses stay inside the
derivation. Raw command calls require only the denotation premise.
`Operational` adds freshness and timestamp consistency to traces.
This module imports no current rule, trace, or simulation proof.
-/

open Incr
namespace Incr.Incr

noncomputable section

variable {sig : Signature}

/-- The seven sandbox-mode rules, as data-carrying derivations. -/
inductive IncrDerivation (m : CommandModel sig) :
    World sig → Head sig → World sig → Option Chunk → Type where
  | pipelineOpen (w : World sig) (p : sig.Probe) (i : Nat) (sb : Sandbox sig)
      (s' s'' : Bytes) (r : Result sig) (buffer' : FMap Nat Chunk) (out : Option Chunk)
      (hbuffer : FMap.get w.buffer i = some ⟨s' ++ s'', .open⟩)
      (hsandbox : FMap.get w.sandbox i = some sb)
      (hinput : sb.input.flag = .open) (houtput : sb.output.flag = .open)
      (hcall : m.denotes p ⟨s', .open⟩ sb.view w.env r)
      (hstatus : r.status = none) (hflag : r.output.flag = .open)
      (hput : updateBuffer w.buffer i r.output ⟨s'', .open⟩ = some (buffer', out)) :
      IncrDerivation m w (.pipeline p i)
        (updateWorld w none ∅ w.cache buffer'
          (w.sandbox[i ↦ (updateSandbox sb ⟨s', .open⟩ r hinput houtput)])) out
  | uncacheClose (w : World sig) (p : sig.Probe) (i : Nat) (sb : Sandbox sig)
      (s : Bytes) (r : Result sig) (x : Nat) (buffer' : FMap Nat Chunk) (out : Option Chunk)
      (hcacheable : ¬ Cacheable m p)
      (hbuffer : FMap.get w.buffer i = some ⟨s, .eof⟩)
      (hsandbox : FMap.get w.sandbox i = some sb)
      (hcall : m.denotes p ⟨s, .eof⟩ sb.view w.env r)
      (hstatus : r.status = some x) (hflag : r.output.flag = .eof)
      (hput : put (w.buffer ∖ i) i r.output = some (buffer', out)) :
      IncrDerivation m w (.pipeline p i)
        (closeWorld w i x (sb.patch ⊎ r.patch) buffer') out
  | cacheCloseMiss (w : World sig) (p : sig.Probe) (i : Nat) (sb : Sandbox sig)
      (s : Bytes) (r : Result sig) (x : Nat) (buffer' : FMap Nat Chunk) (out : Option Chunk)
      (hcacheable : Cacheable m p)
      (hbuffer : FMap.get w.buffer i = some ⟨s, .eof⟩)
      (hsandbox : FMap.get w.sandbox i = some sb)
      (hinput : sb.input.flag = .open) (houtput : sb.output.flag = .open)
      (hmiss : ¬ useCache m w.cache
        (cacheKey m p w.env (sb.input ++'hinput ⟨s, .eof⟩)) w.fs)
      (hcall : m.denotes p ⟨s, .eof⟩ sb.view w.env r)
      (hstatus : r.status = some x) (hflag : r.output.flag = .eof)
      (hput : closeBuffer w.buffer i r.output = some (buffer', out)) :
      IncrDerivation m w (.pipeline p i)
        (updateWorld w (some x) (sb.patch ⊎ r.patch)
          (updateCache w.cache (cacheKey m p w.env (sb.input ++'hinput ⟨s, .eof⟩)) x
            (updateSandbox sb ⟨s, .eof⟩ r hinput houtput) hflag)
          buffer' (w.sandbox ∖ i)) out
  | cacheCloseHit (w : World sig) (p : sig.Probe) (i : Nat) (sb : Sandbox sig)
      (s t : Bytes) (memo : Memo sig) (buffer' : FMap Nat Chunk) (out : Option Chunk)
      (hcacheable : Cacheable m p)
      (hbuffer : FMap.get w.buffer i = some ⟨s, .eof⟩)
      (hsandbox : FMap.get w.sandbox i = some sb)
      (hinput : sb.input.flag = .open) (houtput : sb.output.flag = .open)
      (hmemo : FMap.get w.cache (cacheKey m p w.env (sb.input ++'hinput ⟨s, .eof⟩)) = some memo)
      (hvalid : useCache m w.cache
        (cacheKey m p w.env (sb.input ++'hinput ⟨s, .eof⟩)) w.fs)
      (hguard : memo.output = sb.output ++'houtput ⟨t, .eof⟩)
      (hput : closeBuffer w.buffer i ⟨t, .eof⟩ = some (buffer', out)) :
      IncrDerivation m w (.pipeline p i)
        (updateWorld w (some memo.ec) memo.patch w.cache buffer' (w.sandbox ∖ i)) out
  | uncacheStandalone (w : World sig) (p : sig.Probe) (s : Bytes) (r : Result sig) (x : Nat)
      (hcacheable : ¬ Cacheable m p) (hstdin : w.stdin = ⟨s, .eof⟩)
      (hcall : m.denotes p ⟨s, .eof⟩ w.fs w.env r)
      (hstatus : r.status = some x) :
      IncrDerivation m w (.standalone p)
        (standaloneWorld w x r.patch) (some r.output)
  | cacheStandaloneMiss (w : World sig) (p : sig.Probe) (s : Bytes) (r : Result sig) (x : Nat)
      (hcacheable : Cacheable m p) (hstdin : w.stdin = ⟨s, .eof⟩)
      (hmiss : CacheMiss m w (cacheKey m p w.env ⟨s, .eof⟩))
      (hcall : m.denotes p ⟨s, .eof⟩ w.fs w.env r)
      (hstatus : r.status = some x) (hflag : r.output.flag = .eof) :
      IncrDerivation m w (.standalone p)
        { standaloneWorld w x r.patch with
          cache := FMap.set w.cache (cacheKey m p w.env ⟨s, .eof⟩)
            ⟨x, r.patch, r.reads, r.writes, r.output, hflag⟩ } (some r.output)
  | cacheStandaloneHit (w : World sig) (p : sig.Probe) (s : Bytes) (memo : Memo sig)
      (hcacheable : Cacheable m p) (hstdin : w.stdin = ⟨s, .eof⟩)
      (hmemo : FMap.get w.cache (cacheKey m p w.env ⟨s, .eof⟩) = some memo)
      (hvalid : Valid m memo.reads memo.writes w.fs) (hflag : memo.output.flag = .eof) :
      IncrDerivation m w (.standalone p)
        (standaloneWorld w memo.ec memo.patch) (some memo.output)

/-- The Incr 1.0 rule skeleton. Paper executions additionally satisfy the
shared `Operational` conditions under the model's `DenotationShape` convention. -/
def IncrStep (m : CommandModel sig) (w : World sig) (head : Head sig)
    (w' : World sig) (out : Option Chunk) : Prop :=
  Nonempty (IncrDerivation m w head w' out)

namespace IncrDerivation

variable {m : CommandModel sig}

/-- A hit consumes the unread input, not the memo's whole input. -/
def input : ∀ {w head w' out}, IncrDerivation m w head w' out → Chunk
  | _, _, _, _, .pipelineOpen _ _ _ _ s' _ _ _ _ _ _ _ _ _ _ _ _ => ⟨s', .open⟩
  | _, _, _, _, .uncacheClose _ _ _ _ s _ _ _ _ _ _ _ _ _ _ _ => ⟨s, .eof⟩
  | _, _, _, _, .cacheCloseMiss _ _ _ _ s _ _ _ _ _ _ _ _ _ _ _ _ _ _ => ⟨s, .eof⟩
  | _, _, _, _, .cacheCloseHit _ _ _ _ s _ _ _ _ _ _ _ _ _ _ _ _ _ => ⟨s, .eof⟩
  | _, _, _, _, .uncacheStandalone _ _ s _ _ _ _ _ _ => ⟨s, .eof⟩
  | _, _, _, _, .cacheStandaloneMiss _ _ s _ _ _ _ _ _ _ _ => ⟨s, .eof⟩
  | _, _, _, _, .cacheStandaloneHit _ _ s _ _ _ _ _ _ => ⟨s, .eof⟩

/-- A hit records the whole memo result for dependency and timestamp records. -/
def result : ∀ {w head w' out}, IncrDerivation m w head w' out → Result sig
  | _, _, _, _, .pipelineOpen _ _ _ _ _ _ r _ _ _ _ _ _ _ _ _ _ => r
  | _, _, _, _, .uncacheClose _ _ _ _ _ r _ _ _ _ _ _ _ _ _ _ => r
  | _, _, _, _, .cacheCloseMiss _ _ _ _ _ r _ _ _ _ _ _ _ _ _ _ _ _ _ => r
  | _, _, _, _, .cacheCloseHit _ _ _ _ _ _ memo _ _ _ _ _ _ _ _ _ _ _ => memo.result
  | _, _, _, _, .uncacheStandalone _ _ _ r _ _ _ _ _ => r
  | _, _, _, _, .cacheStandaloneMiss _ _ _ r _ _ _ _ _ _ _ => r
  | _, _, _, _, .cacheStandaloneHit _ _ _ memo _ _ _ _ _ => memo.result

/-- A pipeline hit produces only the output suffix that was not sent before. -/
def produced : ∀ {w head w' out}, IncrDerivation m w head w' out → Chunk
  | _, _, _, _, .pipelineOpen _ _ _ _ _ _ r _ _ _ _ _ _ _ _ _ _ => r.output
  | _, _, _, _, .uncacheClose _ _ _ _ _ r _ _ _ _ _ _ _ _ _ _ => r.output
  | _, _, _, _, .cacheCloseMiss _ _ _ _ _ r _ _ _ _ _ _ _ _ _ _ _ _ _ => r.output
  | _, _, _, _, .cacheCloseHit _ _ _ _ _ tail _ _ _ _ _ _ _ _ _ _ _ _ => ⟨tail, .eof⟩
  | _, _, _, _, .uncacheStandalone _ _ _ r _ _ _ _ _ => r.output
  | _, _, _, _, .cacheStandaloneMiss _ _ _ r _ _ _ _ _ _ _ => r.output
  | _, _, _, _, .cacheStandaloneHit _ _ _ memo _ _ _ _ _ => memo.output

/-- A hit makes no denotation call. Executed calls retain their filesystem argument. -/
def callFS : ∀ {w head w' out}, IncrDerivation m w head w' out → Option (FS sig)
  | _, _, _, _, .pipelineOpen _ _ _ sb _ _ _ _ _ _ _ _ _ _ _ _ _ => some sb.view
  | _, _, _, _, .uncacheClose _ _ _ sb _ _ _ _ _ _ _ _ _ _ _ _ => some sb.view
  | _, _, _, _, .cacheCloseMiss _ _ _ sb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => some sb.view
  | _, _, _, _, .cacheCloseHit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => none
  | _, _, _, _, .uncacheStandalone w _ _ _ _ _ _ _ _ => some w.fs
  | _, _, _, _, .cacheStandaloneMiss w _ _ _ _ _ _ _ _ _ _ => some w.fs
  | _, _, _, _, .cacheStandaloneHit _ _ _ _ _ _ _ _ _ => none

end IncrDerivation

end

end Incr.Incr
