import Incr.Incr.Preservation.Statements

/-! # Cache reuse and hit completion statements (paper `app:proof-reuse`) -/

open Incr
namespace Incr.Incr

variable {sig : Signature}

/-- The conclusion of `lem:paper-cache-reuse` for the exact chosen cache witness
filesystem. -/
def CacheReuseResult (m : CommandModel sig) (p : sig.Probe) (env : Env sig)
    (input : Chunk) (memo : Memo sig) (witnessFS fs : FS sig) : Prop :=
  DepAgree memo.reads memo.writes witnessFS fs ∧
    m.denotes p input fs env memo.result ∧
    ∀ result, m.denotes p input fs env result → ResultEquivalent memo.result result

/-- `lem:paper-hit-completion` and `eq:paper-hit-completion`: a remaining-input
result with the exact
output and dependency equations, patch agreement, freshness, and path bounds. -/
def CacheHitCompletion (m : CommandModel sig) (p : sig.Probe) (env : Env sig)
    (sb : Sandbox sig) (s : Bytes) (memo : Memo sig) (ho : sb.output.flag = .open)
    (forbidden : Set sig.MTime) : Prop :=
  ∃ closing : Result sig,
    m.denotes p ⟨s, .eof⟩ sb.view env closing ∧
    closing.status = some memo.ec ∧ closing.output.flag = .eof ∧
    memo.output = sb.output ++'ho closing.output ∧
    PatchApprox (sb.patch ⊎ closing.patch) memo.patch ∧
    sb.reads ⊎ (closing.reads ↾ (Set.univ \ FMap.dom sb.patch)) = memo.reads ∧
    sb.writes ⊎ (closing.writes ↾ (Set.univ \ FMap.dom sb.patch)) = memo.writes ∧
    (∀ q file, FMap.get closing.patch q = some (.write file) → file.mtime ∉ forbidden) ∧
    FMap.dom sb.patch ∪ FMap.dom closing.patch = FMap.dom memo.patch ∧
    FMap.dom closing.reads ∪ FMap.dom closing.writes ⊆
      FMap.dom memo.reads ∪ FMap.dom memo.writes ∪ FMap.dom sb.patch

/-- The named `Cache-Close-Hit` premises of `app:incr-rules` at the component
and memo fixed by `lem:paper-hit-completion`. This data selects that rule, not
an arbitrary pipeline rule. -/
structure CacheCloseHitApplication (m : CommandModel sig) (selected : World sig)
    (p : sig.Probe) (i : Nat) (sb : Sandbox sig) (s : Bytes) (memo : Memo sig) where
  tail : Bytes
  buffers : FMap Nat Chunk
  out : Option Chunk
  inputOpen : sb.input.flag = .open
  outputOpen : sb.output.flag = .open
  cacheable : Cacheable m p
  buffer : FMap.get selected.buffer i = some ⟨s, .eof⟩
  sandbox : FMap.get selected.sandbox i = some sb
  entry : FMap.get selected.cache
    (cacheKey m p selected.env (sb.input ++'inputOpen ⟨s, .eof⟩)) = some memo
  valid : Valid m memo.reads memo.writes selected.fs
  guard : memo.output = sb.output ++'outputOpen ⟨tail, .eof⟩
  routing : put (selected.buffer ∖ i) i ⟨tail, .eof⟩ = some (buffers, out)

/-- The direct application of the named hit rule and its exact conclusion. -/
def CacheCloseHitApplication.derivation {m : CommandModel sig} {selected : World sig}
    {p : sig.Probe} {i : Nat} {sb : Sandbox sig} {s : Bytes} {memo : Memo sig}
    (hit : CacheCloseHitApplication m selected p i sb s memo) :
    IncrDerivation m selected (.pipeline p i)
      (closeWorld selected i memo.ec memo.patch hit.buffers) hit.out :=
  .cacheCloseHit selected p i sb s hit.tail memo hit.buffers hit.out hit.cacheable
    hit.buffer hit.sandbox hit.inputOpen hit.outputOpen hit.entry
    ((useCache_iff_of_get hit.entry).mpr hit.valid) hit.guard hit.routing

end Incr.Incr
