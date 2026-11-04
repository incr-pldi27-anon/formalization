import Incr.Foundation.Deps
import Incr.Model.State

/-!
# Shared command and cache-witness data

This module supplies the denotation relation, hash and key helpers, exact
result composition, and historical witness data. It defines no command,
cache, host, or execution contract. Each semantics supplies those predicates
separately.
-/

namespace Incr

/-- Abstract relational command semantics. A call can have no result, one
result, or several results. Callers supply the required command assumptions
separately. -/
structure CommandModel (sig : Signature) where
  /-- Content and input hashes (`asm:paper-key`). -/
  hash : Sum Chunk sig.Content → sig.Hash
  /-- `⟦p⟧(input, fs, env) = r` in relational form (`sec:model-command`). -/
  denotes : sig.Probe → Chunk → FS sig → Env sig → Result sig → Prop

def inputHash {sig : Signature} (m : CommandModel sig) (input : Chunk) : sig.Hash :=
  m.hash (.inl input)

def contentHash {sig : Signature} (m : CommandModel sig) (content : sig.Content) : sig.Hash :=
  m.hash (.inr content)

def cacheKey {sig : Signature} (m : CommandModel sig) (p : sig.Probe)
    (env : Env sig) (input : Chunk) : Key sig := ⟨p, env, inputHash m input⟩

def combineResults {sig : Signature} (previous next : Result sig)
    (hout : previous.output.flag = .open) : Result sig :=
  { status := next.status
    patch := previous.patch ⊎ next.patch
    reads := FMap.merge previous.reads
      (FMap.filterKeys (fun q => q ∉ FMap.keys previous.patch) next.reads)
    writes := FMap.merge previous.writes
      (FMap.filterKeys (fun q => q ∉ FMap.keys previous.patch) next.writes)
    output := previous.output ++'hout next.output }

/-- Explicit witness data lets the timestamp premise name historical filesystems. -/
structure CacheWitness (sig : Signature) where
  input : Chunk
  fs : FS sig

abbrev WitnessMap (sig : Signature) := FMap (Key sig) (CacheWitness sig)

noncomputable def cacheRecords {sig : Signature} (cache : Cache sig) : Records sig :=
  cache.entries.toList.flatMap fun kv => patchRecords kv.2.patch

noncomputable def witnessRecords {sig : Signature} (witnesses : WitnessMap sig) : Records sig :=
  witnesses.entries.toList.flatMap fun kv => fsRecords kv.2.fs

end Incr
