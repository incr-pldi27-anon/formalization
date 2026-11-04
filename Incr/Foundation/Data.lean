import Incr.Foundation.FMap

/-!
# Signature, chunks, files, and patches

The abstract sets (`Signature`), byte strings and chunks, file records,
edits, filesystem and patch types, `applyPatch`, and the two agreement
relations `≈` on filesystems and patches (`def:model-approx`).
-/

namespace Incr

noncomputable section

structure Signature where
  Path : Type
  decEqPath : DecidableEq Path
  Content : Type
  decEqContent : DecidableEq Content
  MTime : Type
  decEqMTime : DecidableEq MTime
  Var : Type
  decEqVar : DecidableEq Var
  Value : Type
  decEqValue : DecidableEq Value
  Probe : Type
  decEqProbe : DecidableEq Probe
  Prog : Type
  decEqProg : DecidableEq Prog
  PC : Type
  decEqPC : DecidableEq PC
  Hash : Type
  decEqHash : DecidableEq Hash

attribute [instance] Signature.decEqPath Signature.decEqContent Signature.decEqMTime
  Signature.decEqVar Signature.decEqValue Signature.decEqProbe Signature.decEqProg
  Signature.decEqPC Signature.decEqHash

abbrev Bytes := List UInt8

inductive Flag where
  | open
  | eof
  deriving DecidableEq, Repr

structure Chunk where
  bytes : Bytes
  flag : Flag
  deriving DecidableEq, Repr

namespace Chunk

def emptyOpen : Chunk := ⟨[], .open⟩
def emptyEOF : Chunk := ⟨[], .eof⟩

/--
Proof-carrying concat, matching the paper's partial concat, which is defined
only for an OPEN left operand (`⟨s, open⟩ ++ ⟨s', f⟩ = ⟨s ++ s', f⟩`).
The proof argument makes the eof-left junk case ill-typed, so the open-LHS
discipline (audited 2026-10, `tmp/concat-audit/`) is now enforced by the
typechecker at every call site.
-/
def concat (left right : Chunk) (_h : left.flag = .open) : Chunk :=
  ⟨left.bytes ++ right.bytes, right.flag⟩

end Chunk

/-- `a ++'h b` is proof-carrying chunk concatenation: `Chunk.concat a b h`
with `h : a.flag = .open`. The proof must be the next symbol after `++'`,
mirroring the array-indexing syntax `a[i]'h` and the paper's partial chunk
concatenation `⟨s, open⟩ ++ ⟨s', f⟩` (model.tex). -/
macro:65 a:term "++'" noWs h:ident b:term:66 : term =>
  `(Chunk.concat $a $b $h)

/-- Variant of `++'` that accepts a parenthesised proof term, so proofs that
are not a single identifier can still use the notation: `a ++'(foo.bar) b` is
`Chunk.concat a b foo.bar`. -/
macro:65 a:term "++'" noWs "(" h:term ")" b:term:66 : term =>
  `(Chunk.concat $a $b $h)

structure File (sig : Signature) where
  content : sig.Content
  mtime : sig.MTime
  deriving DecidableEq

theorem File.ext {sig : Signature} {f g : File sig} (hcontent : f.content = g.content)
    (hmtime : f.mtime = g.mtime) : f = g := by
  cases f
  cases g
  simp_all

inductive Edit (sig : Signature) where
  | write (file : File sig)
  | delete
  deriving DecidableEq

abbrev FS (sig : Signature) := FMap sig.Path (File sig)
abbrev Patch (sig : Signature) := FMap sig.Path (Edit sig)

/-- Pointwise description of `merge` via the later map's lookup. -/
theorem FMap.get_merge_elim {K V : Type} [DecidableEq K] {A B : FMap K V} {q : K} :
    FMap.get (A ⊎ B) q = (FMap.get B q).elim (FMap.get A q) some := by
  cases hb : FMap.get B q with
  | none => rw [FMap.get_merge_of_not_mem A B q hb]; rfl
  | some v => rw [FMap.get_merge_of_mem A B q v hb]; rfl

/-- Absent on both sides implies absent in the merge. -/
theorem FMap.get_merge_none {K V : Type} [DecidableEq K] {A B : FMap K V} {q : K}
    (hleft : FMap.get A q = none) (hright : FMap.get B q = none) :
    FMap.get (A ⊎ B) q = none := by
  rw [FMap.get_merge_elim, hright]
  exact hleft

/-- The domain of a merge is the union of the domains. -/
theorem FMap.dom_merge_union {K V : Type} [DecidableEq K] {A B : FMap K V} :
    FMap.dom (FMap.merge A B) = FMap.dom A ∪ FMap.dom B := by
  ext q
  constructor
  · intro hq
    obtain ⟨e, he : FMap.get (FMap.merge A B) q = some e⟩ :=
      Finmap.mem_iff.mp (Finmap.mem_keys.mp hq)
    rw [FMap.get_merge_elim] at he
    cases hb : FMap.get B q with
    | none =>
      rw [hb] at he
      exact Or.inl (Finmap.mem_keys.mpr (Finmap.mem_iff.mpr ⟨e, he⟩))
    | some v =>
      exact Or.inr (Finmap.mem_keys.mpr (Finmap.mem_iff.mpr ⟨v, hb⟩))
  · intro hq
    rcases hq with hq | hq
    · obtain ⟨e, he : FMap.get A q = some e⟩ := Finmap.mem_iff.mp (Finmap.mem_keys.mp hq)
      cases hb : FMap.get B q with
      | none =>
        refine Finmap.mem_keys.mpr (Finmap.mem_iff.mpr ⟨e, ?_⟩)
        change FMap.get (FMap.merge A B) q = some e
        rw [FMap.get_merge_elim, hb, he]
        rfl
      | some v =>
        refine Finmap.mem_keys.mpr (Finmap.mem_iff.mpr ⟨v, ?_⟩)
        change FMap.get (FMap.merge A B) q = some v
        rw [FMap.get_merge_elim, hb]
        rfl
    · obtain ⟨e, he : FMap.get B q = some e⟩ := Finmap.mem_iff.mp (Finmap.mem_keys.mp hq)
      refine Finmap.mem_keys.mpr (Finmap.mem_iff.mpr ⟨e, ?_⟩)
      change FMap.get (FMap.merge A B) q = some e
      rw [FMap.get_merge_elim, he]
      rfl

abbrev Env (sig : Signature) := FMap sig.Var sig.Value
abbrev Reads (sig : Signature) := FMap sig.Path sig.MTime
abbrev Writes (sig : Signature) := FMap sig.Path sig.Hash

/-- The write entries of a patch, viewed as filesystem updates. -/
def patchWrites {sig : Signature} (d : Patch sig) : FS sig :=
  FMap.filterMap (fun _ e => match e with | .write f => some f | .delete => none) d

/-- Apply stored records without changing their timestamps.
Pointwise and independent of entry enumeration order: remove every patched key,
then merge the patch's write records. -/
def applyPatch {sig : Signature} (fs : FS sig) (patch : Patch sig) : FS sig :=
  FMap.merge
    (FMap.filterKeys (fun q => q ∉ FMap.keys patch) fs)
    (patchWrites patch)

infixl:65 " ⊕ " => applyPatch

/-- `def:model-approx`: equality of path presence and contents, without mtimes. -/
def PointwiseFSApprox {sig : Signature} (fs fs' : FS sig) : Prop :=
  ∀ q, (FMap.get fs q).map File.content = (FMap.get fs' q).map File.content

/-- `fs ≈ fs'` — paper filesystem agreement `def:model-approx`: same domains,
same contents, mtimes ignored. -/
instance {sig : Signature} : HasEquiv (FS sig) := ⟨PointwiseFSApprox⟩

theorem PointwiseFSApprox.symm {sig : Signature} {fs fs' : FS sig} (h : fs ≈ fs') :
    fs' ≈ fs :=
  fun q => (h q).symm

theorem PointwiseFSApprox.refl {sig : Signature} (fs : FS sig) : fs ≈ fs :=
  fun _ => rfl

theorem PointwiseFSApprox.restrict {sig : Signature} {fs fs' : FS sig} {s : Set sig.Path}
    (h : fs ≈ fs') :
    (fs ↾ s) ≈ (fs' ↾ s) := by
  classical
  intro q
  rw [FMap.get_restrict, FMap.get_restrict]
  by_cases hq : q ∈ s <;> simp [hq, h q]

def editContent {sig : Signature} : Edit sig → Option sig.Content
  | .write f => some f.content
  | .delete => none

/-- The outer option distinguishes an absent patch entry from a deletion. -/
def PointwisePatchApprox {sig : Signature} (d d' : Patch sig) : Prop :=
  ∀ q, (FMap.get d q).map editContent = (FMap.get d' q).map editContent

/-- `Δ ≈ Δ'` — paper patch agreement: same domains, entrywise both delete or
same contents (outer option distinguishes absent from delete). -/
instance {sig : Signature} : HasEquiv (Patch sig) := ⟨PointwisePatchApprox⟩

theorem PointwiseFSApprox.equiv {sig : Signature} {fs fs' : FS sig} :
    (fs ≈ fs') = PointwiseFSApprox fs fs' := rfl

theorem PointwisePatchApprox.equiv {sig : Signature} {d d' : Patch sig} :
    (d ≈ d') = PointwisePatchApprox d d' := rfl

theorem PointwisePatchApprox.symm {sig : Signature} {d d' : Patch sig} (h : d ≈ d') :
    d' ≈ d :=
  fun q => (h q).symm

theorem editContent_of_eq_none {sig : Signature} {e : Edit sig} (h : editContent e = none) :
    e = .delete := by
  cases e <;> simp_all [editContent]

theorem editContent_of_eq_some {sig : Signature} {e : Edit sig} {c : sig.Content}
    (h : editContent e = some c) : ∃ f, e = .write f ∧ f.content = c := by
  cases e <;> simp_all [editContent]

theorem editContent_map_eq_none {sig : Signature} {o : Option (Edit sig)}
    (h : o.map editContent = some none) : o = some .delete := by
  cases o with
  | none => simp at h
  | some e =>
    have hc : editContent e = none := by simpa using h
    rw [editContent_of_eq_none hc]

theorem editContent_map_eq_some {sig : Signature} {o : Option (Edit sig)} {c : sig.Content}
    (h : o.map editContent = some (some c)) : ∃ f, o = some (.write f) ∧ f.content = c := by
  cases o with
  | none => simp at h
  | some e =>
    have hc : editContent e = some c := by simpa using h
    obtain ⟨f, hfl, hfc⟩ := editContent_of_eq_some hc
    exact ⟨f, by rw [hfl], hfc⟩

theorem PointwisePatchApprox.write {sig : Signature} {d d' : Patch sig} (h : d ≈ d')
    {q : sig.Path} {f : File sig} (hd : FMap.get d q = some (.write f)) :
    ∃ f', FMap.get d' q = some (.write f') ∧ f'.content = f.content := by
  have hq := h q
  rw [hd] at hq
  simp only [Option.map_some, editContent] at hq
  exact editContent_map_eq_some hq.symm

theorem PointwisePatchApprox.delete {sig : Signature} {d d' : Patch sig} (h : d ≈ d')
    {q : sig.Path} (hd : FMap.get d q = some .delete) : FMap.get d' q = some .delete := by
  have hq := h q
  rw [hd] at hq
  simp only [Option.map_some, editContent] at hq
  exact editContent_map_eq_none hq.symm

theorem PointwisePatchApprox.none {sig : Signature} {d d' : Patch sig} (h : d ≈ d')
    {q : sig.Path} (hd : FMap.get d q = none) : FMap.get d' q = none := by
  have hq := h q
  rw [hd] at hq
  simpa using hq.symm

theorem PointwisePatchApprox.trans {sig : Signature} {d₁ d₂ d₃ : Patch sig}
    (h₁ : PointwisePatchApprox d₁ d₂) (h₂ : PointwisePatchApprox d₂ d₃) : PointwisePatchApprox d₁ d₃ :=
  fun q => (h₁ q).trans (h₂ q)

theorem PointwisePatchApprox.dom_eq {sig : Signature} {d d' : Patch sig} (h : d ≈ d') :
    FMap.dom d = FMap.dom d' := by
  ext q
  constructor
  · intro hq
    obtain ⟨e, he : FMap.get d q = some e⟩ := Finmap.mem_iff.mp (Finmap.mem_keys.mp hq)
    have hq' := h q
    rw [he] at hq'
    simp only [Option.map_some] at hq'
    cases hd' : FMap.get d' q with
    | none => rw [hd'] at hq'; simp at hq'
    | some e' => exact Finmap.mem_keys.mpr (Finmap.mem_iff.mpr ⟨e', hd'⟩)
  · intro hq
    obtain ⟨e, he : FMap.get d' q = some e⟩ := Finmap.mem_iff.mp (Finmap.mem_keys.mp hq)
    have hq' := (h q).symm
    rw [he] at hq'
    simp only [Option.map_some] at hq'
    cases hd : FMap.get d q with
    | none => rw [hd] at hq'; simp at hq'
    | some e' => exact Finmap.mem_keys.mpr (Finmap.mem_iff.mpr ⟨e', hd⟩)

/-! ## Pointwise patch application -/

theorem applyPatch_get_write {sig : Signature} {fs : FS sig} {d : Patch sig} {q : sig.Path}
    {f : File sig} (hd : FMap.get d q = some (.write f)) :
    FMap.get (applyPatch fs d) q = some f := by
  rw [applyPatch]
  apply FMap.get_merge_of_mem
  rw [patchWrites, FMap.get_filterMap]
  simp only [hd, Option.bind_some]

theorem applyPatch_get_delete {sig : Signature} {fs : FS sig} {d : Patch sig} {q : sig.Path}
    (hd : FMap.get d q = some .delete) : FMap.get (applyPatch fs d) q = none := by
  have hmem : q ∈ FMap.keys d :=
    Finmap.mem_keys.mpr (Finmap.mem_iff.mpr ⟨.delete, by simpa only [FMap.get] using hd⟩)
  rw [applyPatch]
  rw [FMap.get_merge_of_not_mem (earlier := FMap.filterKeys (fun q => q ∉ FMap.keys d) fs)
    (later := patchWrites d) q (by
      rw [patchWrites, FMap.get_filterMap]
      simp only [hd, Option.bind_some])]
  rw [FMap.get_filterKeys]
  rw [ite_eq_right (fun h => h hmem)]

theorem applyPatch_get_none {sig : Signature} {fs : FS sig} {d : Patch sig} {q : sig.Path}
    (hd : FMap.get d q = none) : FMap.get (applyPatch fs d) q = FMap.get fs q := by
  have hnot : q ∉ FMap.keys d := by
    intro hmem
    obtain ⟨v, hv⟩ := Finmap.mem_iff.mp (Finmap.mem_keys.mp hmem)
    rw [FMap.get] at hd
    rw [hd] at hv
    simp at hv
  rw [applyPatch]
  rw [FMap.get_merge_of_not_mem (earlier := FMap.filterKeys (fun q => q ∉ FMap.keys d) fs)
    (later := patchWrites d) q (by
      rw [patchWrites, FMap.get_filterMap]
      simp only [hd, Option.bind_none])]
  rw [FMap.get_filterKeys]
  rw [ite_eq_left hnot]

theorem applyPatch_empty {sig : Signature} (fs : FS sig) : applyPatch fs ∅ = fs := by
  apply Finmap.ext_lookup
  intro q
  exact applyPatch_get_none (Finmap.lookup_empty q)


end

end Incr
