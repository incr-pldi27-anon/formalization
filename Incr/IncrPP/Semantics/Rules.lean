import Incr.IncrPP.Semantics.Common

/-!
# The seven raw live probe rules

These constructors retain the rule witnesses from Appendix E. Calls and
validation use the current shared filesystem. An executing pipeline step
applies only its current result patch, not its accumulated patch.
Misses have all three cache policies and no cache-absence premise.

P1 keeps call freshness, replay timestamps, and prefix record consistency in
the ambient execution layer. Partial concatenation uses explicit open-left
typing evidence. These flags are not extra denotation assumptions.
-/

namespace Incr.IncrPP

noncomputable section

variable {sig : Signature}

/-- The four pipeline and three standalone branches of Appendix E. -/
inductive LiveDerivation (m : CommandModel sig) :
    World sig → Head sig → World sig → Option Chunk → Type where
  | pipelineOpen (w : World sig) (p : sig.Probe) (i : Nat) (sb : Sandbox sig)
      (s' s'' : Bytes) (r : Result sig) (buffer' : FMap Nat Chunk) (out : Option Chunk)
      (hbuffer : FMap.get w.buffer i = some ⟨s' ++ s'', .open⟩)
      (hsandbox : FMap.get w.sandbox i = some sb)
      (hinput : sb.input.flag = .open) (houtput : sb.output.flag = .open)
      (hcall : m.denotes p ⟨s', .open⟩ w.fs w.env r)
      (hstatus : r.status = none) (hflag : r.output.flag = .open)
      (hput : updateBuffer w.buffer i r.output ⟨s'', .open⟩ = some (buffer', out)) :
      LiveDerivation m w (.pipeline p i)
        (updateWorld w none r.patch w.cache buffer'
          (w.sandbox[i ↦ (updateSandbox sb ⟨s', .open⟩ r hinput houtput)])) out
  | uncacheClose (w : World sig) (p : sig.Probe) (i : Nat) (sb : Sandbox sig)
      (s : Bytes) (r : Result sig) (ec' : Nat) (buffer' : FMap Nat Chunk) (out : Option Chunk)
      (hcacheable : ¬ Cacheable m p)
      (hbuffer : FMap.get w.buffer i = some ⟨s, .eof⟩)
      (hsandbox : FMap.get w.sandbox i = some sb)
      (hcall : m.denotes p ⟨s, .eof⟩ w.fs w.env r)
      (hstatus : r.status = some ec') (hflag : r.output.flag = .eof)
      (hput : put (w.buffer ∖ i) i r.output = some (buffer', out)) :
      LiveDerivation m w (.pipeline p i) (closeWorld w i ec' r.patch buffer') out
  | cacheCloseMiss (w : World sig) (p : sig.Probe) (i : Nat) (sb : Sandbox sig)
      (s : Bytes) (r : Result sig) (ec' : Nat) (buffer' : FMap Nat Chunk) (out : Option Chunk)
      (cache' : Cache sig)
      (hcacheable : Cacheable m p)
      (hbuffer : FMap.get w.buffer i = some ⟨s, .eof⟩)
      (hsandbox : FMap.get w.sandbox i = some sb)
      (hinput : sb.input.flag = .open) (houtput : sb.output.flag = .open)
      (hcall : m.denotes p ⟨s, .eof⟩ w.fs w.env r)
      (hstatus : r.status = some ec') (hflag : r.output.flag = .eof)
      (hcache : CacheUpdate w.cache (cacheKey m p w.env (sb.input ++'hinput ⟨s, .eof⟩))
        (accumulatedMemo sb ⟨s, .eof⟩ r ec' hinput houtput hflag) cache')
      (hput : closeBuffer w.buffer i r.output = some (buffer', out)) :
      LiveDerivation m w (.pipeline p i)
        (updateWorld w (some ec') r.patch cache' buffer' (w.sandbox ∖ i)) out
  | cacheCloseHit (w : World sig) (p : sig.Probe) (i : Nat) (sb : Sandbox sig)
      (s t : Bytes) (memo : Memo sig) (delta'' : Patch sig)
      (buffer' : FMap Nat Chunk) (out : Option Chunk)
      (hcacheable : Cacheable m p) (hempty : sb.patch = ∅)
      (hbuffer : FMap.get w.buffer i = some ⟨s, .eof⟩)
      (hsandbox : FMap.get w.sandbox i = some sb)
      (hinput : sb.input.flag = .open) (houtput : sb.output.flag = .open)
      (hmemo : FMap.get w.cache (cacheKey m p w.env (sb.input ++'hinput ⟨s, .eof⟩)) = some memo)
      (hvalid : useCache m w.cache
        (cacheKey m p w.env (sb.input ++'hinput ⟨s, .eof⟩)) w.fs)
      (hguard : memo.output = sb.output ++'houtput ⟨t, .eof⟩)
      (hpatch : PatchApprox delta'' memo.patch)
      (hput : closeBuffer w.buffer i ⟨t, .eof⟩ = some (buffer', out)) :
      LiveDerivation m w (.pipeline p i)
        (updateWorld w (some memo.ec) delta'' w.cache buffer' (w.sandbox ∖ i)) out
  | uncacheStandalone (w : World sig) (p : sig.Probe) (s : Bytes) (r : Result sig) (ec' : Nat)
      (hcacheable : ¬ Cacheable m p) (hstdin : w.stdin = ⟨s, .eof⟩)
      (hcall : m.denotes p ⟨s, .eof⟩ w.fs w.env r) (hstatus : r.status = some ec') :
      LiveDerivation m w (.standalone p) (standaloneWorld w ec' r.patch) (some r.output)
  | cacheStandaloneMiss (w : World sig) (p : sig.Probe) (s : Bytes) (r : Result sig) (ec' : Nat)
      (cache' : Cache sig)
      (hcacheable : Cacheable m p) (hstdin : w.stdin = ⟨s, .eof⟩)
      (hcall : m.denotes p ⟨s, .eof⟩ w.fs w.env r)
      (hstatus : r.status = some ec') (hflag : r.output.flag = .eof)
      (hcache : CacheUpdate w.cache (cacheKey m p w.env ⟨s, .eof⟩)
        ⟨ec', r.patch, r.reads, r.writes, r.output, hflag⟩ cache') :
      LiveDerivation m w (.standalone p)
        { standaloneWorld w ec' r.patch with cache := cache' } (some r.output)
  | cacheStandaloneHit (w : World sig) (p : sig.Probe) (s : Bytes) (memo : Memo sig)
      (delta'' : Patch sig)
      (hcacheable : Cacheable m p) (hstdin : w.stdin = ⟨s, .eof⟩)
      (hmemo : FMap.get w.cache (cacheKey m p w.env ⟨s, .eof⟩) = some memo)
      (hvalid : Valid m memo.reads memo.writes w.fs)
      (hpatch : PatchApprox delta'' memo.patch) :
      LiveDerivation m w (.standalone p)
        (standaloneWorld w memo.ec delta'') (some memo.output)

/-- The existential raw live probe judgment. Ambient execution adds P1 conditions. -/
def LiveStep (m : CommandModel sig) (w : World sig) (head : Head sig)
    (next : World sig) (out : Option Chunk) : Prop :=
  Nonempty (LiveDerivation m w head next out)

end
end IncrPP
end Incr
