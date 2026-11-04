import Incr.Foundation.Data

/-!
# Execution state

Command results, cache keys and memos, the cache, sandbox records with their
accumulation, the world state, probe heads, and output routing (`put`).
-/

namespace Incr

noncomputable section

structure Result (sig : Signature) where
  status : Option Nat
  patch : Patch sig
  reads : Reads sig
  writes : Writes sig
  output : Chunk

structure Key (sig : Signature) where
  probe : sig.Probe
  env : Env sig
  inputHash : sig.Hash
  deriving DecidableEq

/-- A saved command result. The paper's type carries the invariant "A memo's
`sout` is complete and EOF-marked" (`model.tex`, fig:model-definitions), so
the output flag is pinned on the type. Rule premises (`Semantics.lean`) and
`WellFormedCache` also re-derive the flag per use. -/
structure Memo (sig : Signature) where
  ec : Nat
  patch : Patch sig
  reads : Reads sig
  writes : Writes sig
  output : Chunk
  output_eof : output.flag = .eof

def Memo.result {sig : Signature} (m : Memo sig) : Result sig :=
  ⟨some m.ec, m.patch, m.reads, m.writes, m.output⟩

abbrev Cache (sig : Signature) := FMap (Key sig) (Memo sig)

structure Sandbox (sig : Signature) where
  base : FS sig
  input : Chunk
  reads : Reads sig
  writes : Writes sig
  patch : Patch sig
  output : Chunk

def Sandbox.initial {sig : Signature} (fs : FS sig) : Sandbox sig :=
  ⟨fs, .emptyOpen, ∅, ∅, ∅, .emptyOpen⟩

def Sandbox.view {sig : Signature} (sb : Sandbox sig) : FS sig :=
  applyPatch sb.base sb.patch

def Sandbox.accumulate {sig : Signature} (sb : Sandbox sig)
    (input : Chunk) (r : Result sig) (hinput : sb.input.flag = .open)
    (houtput : sb.output.flag = .open) : Sandbox sig :=
  { sb with
    input := sb.input ++'hinput input
    reads := sb.reads ⊎ (FMap.filterKeys (fun q => q ∉ FMap.keys sb.patch) r.reads)
    writes := sb.writes ⊎ (FMap.filterKeys (fun q => q ∉ FMap.keys sb.patch) r.writes)
    patch := sb.patch ⊎ r.patch
    output := sb.output ++'houtput r.output }

@[simp] theorem Sandbox.accumulate_base {sig : Signature} (sb : Sandbox sig)
    (input : Chunk) (r : Result sig) (hinput : sb.input.flag = .open)
    (houtput : sb.output.flag = .open) : (sb.accumulate input r hinput houtput).base = sb.base := rfl

@[simp] theorem Sandbox.accumulate_input_flag {sig : Signature} (sb : Sandbox sig)
    (input : Chunk) (r : Result sig) (hinput : sb.input.flag = .open)
    (houtput : sb.output.flag = .open) :
    (sb.accumulate input r hinput houtput).input.flag = input.flag := rfl

@[simp] theorem Sandbox.accumulate_output_flag {sig : Signature} (sb : Sandbox sig)
    (input : Chunk) (r : Result sig) (hinput : sb.input.flag = .open)
    (houtput : sb.output.flag = .open) :
    (sb.accumulate input r hinput houtput).output.flag = r.output.flag := rfl

/-- The accumulated patch's domain is the union of the old domain and the
result patch's domain (`lem:paper-bisim-prefix` bookkeeping). -/
theorem Sandbox.accumulate_patch_dom {sig : Signature} (sb : Sandbox sig) (input : Chunk)
    (r : Result sig) (hinput : sb.input.flag = .open) (houtput : sb.output.flag = .open) :
    FMap.dom (sb.accumulate input r hinput houtput).patch =
      FMap.dom sb.patch ∪ FMap.dom r.patch := by
  change FMap.dom (sb.patch ⊎ r.patch) = FMap.dom sb.patch ∪ FMap.dom r.patch
  exact FMap.dom_merge_union

/-- Per-step reads accumulation: the restricted merge drops exactly the result
reads whose keys already occur in the accumulated patch. -/
theorem Sandbox.accumulate_reads_dom {sig : Signature} (sb : Sandbox sig) (input : Chunk)
    (r : Result sig) (hinput : sb.input.flag = .open) (houtput : sb.output.flag = .open) :
    FMap.dom (sb.accumulate input r hinput houtput).reads =
      FMap.dom sb.reads ∪ {q | q ∈ FMap.dom r.reads ∧ q ∉ FMap.keys sb.patch} := by
  change FMap.dom (FMap.merge sb.reads
    (FMap.filterKeys (fun q => q ∉ FMap.keys sb.patch) r.reads)) = _
  rw [FMap.dom_merge_union]
  ext q
  simp only [Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · intro hq
    rcases hq with hq | hq
    · exact Or.inl hq
    · obtain ⟨v, hv : FMap.get (FMap.filterKeys (fun q => q ∉ FMap.keys sb.patch) r.reads) q
        = some v⟩ := Finmap.mem_iff.mp (Finmap.mem_keys.mp hq)
      rw [FMap.get_filterKeys_eq_some] at hv
      exact Or.inr ⟨Finmap.mem_keys.mpr (Finmap.mem_iff.mpr ⟨v, hv.2⟩), hv.1⟩
  · intro hq
    rcases hq with hq | hq
    · exact Or.inl hq
    · obtain ⟨v, hv : FMap.get r.reads q = some v⟩ :=
        Finmap.mem_iff.mp (Finmap.mem_keys.mp hq.1)
      refine Or.inr (Finmap.mem_keys.mpr (Finmap.mem_iff.mpr ⟨v, ?_⟩))
      change FMap.get (FMap.filterKeys (fun q => q ∉ FMap.keys sb.patch) r.reads) q = some v
      rw [FMap.get_filterKeys_eq_some]
      exact ⟨hq.2, hv⟩

/-- Per-step writes accumulation: mirror of `Sandbox.accumulate_reads_dom`. -/
theorem Sandbox.accumulate_writes_dom {sig : Signature} (sb : Sandbox sig) (input : Chunk)
    (r : Result sig) (hinput : sb.input.flag = .open) (houtput : sb.output.flag = .open) :
    FMap.dom (sb.accumulate input r hinput houtput).writes =
      FMap.dom sb.writes ∪ {q | q ∈ FMap.dom r.writes ∧ q ∉ FMap.keys sb.patch} := by
  change FMap.dom (FMap.merge sb.writes
    (FMap.filterKeys (fun q => q ∉ FMap.keys sb.patch) r.writes)) = _
  rw [FMap.dom_merge_union]
  ext q
  simp only [Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · intro hq
    rcases hq with hq | hq
    · exact Or.inl hq
    · obtain ⟨v, hv : FMap.get (FMap.filterKeys (fun q => q ∉ FMap.keys sb.patch) r.writes) q
        = some v⟩ := Finmap.mem_iff.mp (Finmap.mem_keys.mp hq)
      rw [FMap.get_filterKeys_eq_some] at hv
      exact Or.inr ⟨Finmap.mem_keys.mpr (Finmap.mem_iff.mpr ⟨v, hv.2⟩), hv.1⟩
  · intro hq
    rcases hq with hq | hq
    · exact Or.inl hq
    · obtain ⟨v, hv : FMap.get r.writes q = some v⟩ :=
        Finmap.mem_iff.mp (Finmap.mem_keys.mp hq.1)
      refine Or.inr (Finmap.mem_keys.mpr (Finmap.mem_iff.mpr ⟨v, ?_⟩))
      change FMap.get (FMap.filterKeys (fun q => q ∉ FMap.keys sb.patch) r.writes) q = some v
      rw [FMap.get_filterKeys_eq_some]
      exact ⟨hq.2, hv⟩

structure World (sig : Signature) where
  ec : Nat
  fs : FS sig
  env : Env sig
  cache : Cache sig
  buffer : FMap Nat Chunk
  sandbox : FMap Nat (Sandbox sig)
  stdin : Chunk
  pc : sig.PC

inductive Head (sig : Signature) where
  | standalone (probe : sig.Probe)
  | pipeline (probe : sig.Probe) (slot : Nat)

def Head.probe {sig : Signature} : Head sig → sig.Probe
  | .standalone p => p
  | .pipeline p _ => p

/-- Routing is undefined when the successor buffer already has EOF. -/
def put (buffers : FMap Nat Chunk) (slot : Nat) (output : Chunk) :
    Option (FMap Nat Chunk × Option Chunk) :=
  match FMap.get buffers (slot + 1) with
  | none => some (buffers, some output)
  | some ⟨s, .open⟩ => some (buffers[(slot + 1) ↦ ⟨s ++ output.bytes, output.flag⟩], none)
  | some ⟨_, .eof⟩ => none

theorem put_domain {buffers buffers' : FMap Nat Chunk} {slot : Nat} {output : Chunk}
    {returned : Option Chunk} (hput : put buffers slot output = some (buffers', returned)) :
    FMap.dom buffers' = FMap.dom buffers := by
  unfold put at hput
  cases hnext : FMap.get buffers (slot + 1) with
  | none =>
      simp only [hnext, Option.some.injEq, Prod.mk.injEq] at hput
      cases hput
      subst buffers'
      rfl
  | some next =>
      cases next with
      | mk bytes flag =>
        cases flag with
        | «open» =>
            simp only [hnext, Option.some.injEq, Prod.mk.injEq] at hput
            cases hput
            subst buffers'
            apply FMap.dom_set_of_get
            exact ⟨⟨bytes, .open⟩, hnext⟩
        | eof =>
            simp only [hnext] at hput
            exact absurd hput (by simp)

/-- `put` returns output to the host exactly at the slot with no successor
buffer. Under the `lem:paper-buffers` domain invariant (the buffer domain is
precisely the unclosed slots), this is the pipeline's last slot. -/
theorem put_returned_iff {buffers buffers' : FMap Nat Chunk} {slot : Nat} {output : Chunk}
    {returned : Option Chunk} (hput : put buffers slot output = some (buffers', returned)) :
    returned = some output ↔ FMap.get buffers (slot + 1) = none := by
  unfold put at hput
  cases hnext : FMap.get buffers (slot + 1) with
  | none =>
      simp only [hnext, Option.some.injEq, Prod.mk.injEq] at hput
      obtain ⟨rfl, rfl⟩ := hput
      simp
  | some next =>
      cases next with
      | mk bytes flag =>
        cases flag with
        | «open» =>
            simp only [hnext, Option.some.injEq, Prod.mk.injEq] at hput
            obtain ⟨rfl, rfl⟩ := hput
            simp
        | eof =>
            simp only [hnext] at hput
            exact absurd hput (by simp)


variable {sig : Signature}

/-- Add one call's input, output, effects, and external dependencies. -/
def updateSandbox (sb : Sandbox sig) (input : Chunk) (r : Result sig)
    (hinput : sb.input.flag = .open) (houtput : sb.output.flag = .open) : Sandbox sig :=
  sb.accumulate input r hinput houtput

/-- Store an already accumulated sandbox. No further accumulation occurs here. -/
def updateCache (cache : Cache sig) (key : Key sig) (x : Nat) (sb : Sandbox sig)
    (houtput : sb.output.flag = .eof) : Cache sig :=
  FMap.set cache key ⟨x, sb.patch, sb.reads, sb.writes, sb.output, houtput⟩

/-- Keep unread input and forward this call's output. -/
def updateBuffer (buffer : FMap Nat Chunk) (i : Nat) (output input : Chunk) :
    Option (FMap Nat Chunk × Option Chunk) :=
  put (buffer[i ↦ input]) i output

/-- Remove a closed slot and forward its output. -/
def closeBuffer (buffer : FMap Nat Chunk) (i : Nat) (output : Chunk) :
    Option (FMap Nat Chunk × Option Chunk) :=
  put (buffer ∖ i) i output

/-- The paper's world update applies even an empty patch literally. -/
def updateWorld (w : World sig) (x : Option Nat) (patch : Patch sig)
    (cache : Cache sig) (buffer : FMap Nat Chunk) (sandbox : FMap Nat (Sandbox sig)) :
    World sig :=
  { w with
    ec := x.getD w.ec
    fs := applyPatch w.fs patch
    cache := cache
    buffer := buffer
    sandbox := sandbox }

@[simp] theorem updateWorld_fs (w : World sig) (x : Option Nat) (patch : Patch sig)
    (cache : Cache sig) (buffer : FMap Nat Chunk) (sandbox : FMap Nat (Sandbox sig)) :
    (updateWorld w x patch cache buffer sandbox).fs = applyPatch w.fs patch := rfl

@[simp] theorem updateWorld_ec (w : World sig) (x : Option Nat) (patch : Patch sig)
    (cache : Cache sig) (buffer : FMap Nat Chunk) (sandbox : FMap Nat (Sandbox sig)) :
    (updateWorld w x patch cache buffer sandbox).ec = x.getD w.ec := rfl

@[simp] theorem updateWorld_cache (w : World sig) (x : Option Nat) (patch : Patch sig)
    (cache : Cache sig) (buffer : FMap Nat Chunk) (sandbox : FMap Nat (Sandbox sig)) :
    (updateWorld w x patch cache buffer sandbox).cache = cache := rfl

@[simp] theorem updateWorld_buffer (w : World sig) (x : Option Nat) (patch : Patch sig)
    (cache : Cache sig) (buffer : FMap Nat Chunk) (sandbox : FMap Nat (Sandbox sig)) :
    (updateWorld w x patch cache buffer sandbox).buffer = buffer := rfl

@[simp] theorem updateWorld_sandbox (w : World sig) (x : Option Nat) (patch : Patch sig)
    (cache : Cache sig) (buffer : FMap Nat Chunk) (sandbox : FMap Nat (Sandbox sig)) :
    (updateWorld w x patch cache buffer sandbox).sandbox = sandbox := rfl

/-- Normalize the literal empty application only when a proof needs the old world shape. -/
@[simp] theorem updateWorld_none_empty (w : World sig) (cache : Cache sig)
    (buffer : FMap Nat Chunk) (sandbox : FMap Nat (Sandbox sig)) :
    updateWorld w none ∅ cache buffer sandbox =
      { w with cache := cache, buffer := buffer, sandbox := sandbox } := by
  simp [updateWorld, applyPatch_empty]

end

end Incr
