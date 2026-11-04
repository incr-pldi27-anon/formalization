import Incr.Model.CommandModel

/-!
# Paper-shaped model predicates for recorded Incr 1.0

These predicates retain the printed clauses of `def:model-approx`,
`def:model-cacheable`, `def:paper-cache-wf`, and Definition 3.1
(`def:model-valid`). Shared data types and operations remain in `Spec`. Legacy contracts
are not imported or changed. Optional lookups encode partial-map projections within each
clause; they do not replace the separate domain requirements.
-/

namespace Incr

noncomputable section

variable {sig : Signature}

/-- `def:model-approx` (agreement up to mtime): equal domains, then equal
contents at every path in that domain. -/
def FSApprox (fs fs' : FS sig) : Prop :=
  FMap.dom fs = FMap.dom fs' ∧
    ∀ q ∈ FMap.dom fs,
      (FMap.get fs q).map File.content = (FMap.get fs' q).map File.content

/-- The paper's two filesystem clauses imply pointwise observed contents. -/
theorem FSApprox.contents {fs fs' : FS sig} (h : FSApprox fs fs') (q : sig.Path) :
    (FMap.get fs q).map File.content = (FMap.get fs' q).map File.content := by
  classical
  by_cases hq : q ∈ FMap.dom fs
  · exact h.2 q hq
  · have hq' : q ∉ FMap.dom fs' := by rw [← h.1]; exact hq
    have hn : FMap.get fs q = none :=
      FMap.get_eq_none.mpr (fun hm => hq (Finmap.mem_keys.mpr hm))
    have hn' : FMap.get fs' q = none :=
      FMap.get_eq_none.mpr (fun hm => hq' (Finmap.mem_keys.mpr hm))
    rw [hn, hn']

/-- Pointwise observation equality supplies the two printed `def:model-approx`
clauses. -/
theorem FSApprox.of_contents {fs fs' : FS sig}
    (h : ∀ q, (FMap.get fs q).map File.content =
      (FMap.get fs' q).map File.content) : FSApprox fs fs' := by
  classical
  refine ⟨?_, fun q _ => h q⟩
  ext q
  constructor
  · intro hq
    obtain ⟨file, hf⟩ := Finmap.mem_iff.mp (Finmap.mem_keys.mp hq)
    cases hg : FMap.get fs' q with
    | none =>
      have he := h q
      rw [show FMap.get fs q = some file from hf, hg] at he
      contradiction
    | some file' => exact Finmap.mem_keys.mpr (Finmap.mem_iff.mpr ⟨file', hg⟩)
  · intro hq
    obtain ⟨file, hg⟩ := Finmap.mem_iff.mp (Finmap.mem_keys.mp hq)
    cases hf : FMap.get fs q with
    | none =>
      have he := h q
      rw [hf, show FMap.get fs' q = some file from hg] at he
      contradiction
    | some file' => exact Finmap.mem_keys.mpr (Finmap.mem_iff.mpr ⟨file', hf⟩)

/-- `def:model-approx` (patch agreement): equal patch domains, then equal
deletion markers or write contents. -/
def PatchApprox (patch patch' : Patch sig) : Prop :=
  FMap.dom patch = FMap.dom patch' ∧
    ∀ q ∈ FMap.dom patch,
      (FMap.get patch q).map editContent = (FMap.get patch' q).map editContent

/-- Definition 3.1: domain coverage, read timestamps, then write-content hashes. -/
def Valid (m : CommandModel sig) (reads : Reads sig) (writes : Writes sig)
    (fs : FS sig) : Prop :=
  FMap.dom reads ∪ FMap.dom writes ⊆ FMap.dom fs ∧
    (∀ q t file, FMap.get reads q = some t → FMap.get fs q = some file →
      file.mtime = t) ∧
    (∀ q hash file, FMap.get writes q = some hash → FMap.get fs q = some file →
      contentHash m file.content = hash)

/-- The tuple equation and patch agreement in the `def:model-cacheable`
universal clause. -/
def ResultEquivalent (r r' : Result sig) : Prop :=
  (r'.status, r'.reads, r'.writes, r'.output) =
    (r.status, r.reads, r.writes, r.output) ∧ PatchApprox r'.patch r.patch

/-- `def:model-cacheable` (cacheability): existence of a result, then agreement
of every admitted result. -/
def Cacheable (m : CommandModel sig) (p : sig.Probe) : Prop :=
  ∀ input fs env r, m.denotes p input fs env r →
    ∀ fs', DepAgree r.reads r.writes fs fs' →
      (∃ r', m.denotes p input fs' env r') ∧
      (∀ r', m.denotes p input fs' env r' → ResultEquivalent r r')

/-- A present memo can be reused exactly when its dependencies are valid.
The memo output is not tested. -/
def useCache (m : CommandModel sig) (cache : Cache sig) (key : Key sig) (fs : FS sig) : Prop :=
  ∃ memo, FMap.get cache key = some memo ∧ Valid m memo.reads memo.writes fs

/-- A known lookup identifies the memo selected by `useCache`. -/
theorem useCache_iff_of_get {m : CommandModel sig} {cache : Cache sig} {key : Key sig}
    {fs : FS sig} {memo : Memo sig} (hget : FMap.get cache key = some memo) :
    useCache m cache key fs ↔ Valid m memo.reads memo.writes fs := by
  constructor
  · rintro ⟨memo', hget', hvalid⟩
    have : memo' = memo := Option.some.inj (hget'.symm.trans hget)
    subst memo'
    exact hvalid
  · exact fun hvalid => ⟨memo, hget, hvalid⟩

/-- A missing entry or invalid live dependencies selects a cache miss. -/
def CacheMiss (m : CommandModel sig) (world : World sig) (key : Key sig) : Prop :=
  FMap.get world.cache key = none ∨
    ∃ memo, FMap.get world.cache key = some memo ∧
      ¬ Valid m memo.reads memo.writes world.fs

/-- The historical miss disjunction is the negation of the paper helper. -/
theorem cacheMiss_iff_not_useCache (m : CommandModel sig) (w : World sig) (key : Key sig) :
    CacheMiss m w key ↔ ¬ useCache m w.cache key w.fs := by
  classical
  cases hget : FMap.get w.cache key with
  | none => simp [CacheMiss, useCache, hget]
  | some memo => simp [CacheMiss, useCache, hget]

/-- `def:paper-cache-wf` (cache well-formedness): retain the historical probe,
environment, input, filesystem, and whole-key equation inside each entry's
existential certificate. -/
def WellFormedCache (m : CommandModel sig) (cache : Cache sig) : Prop :=
  ∀ key memo, FMap.get cache key = some memo →
    ∃ p env input fs,
      Cacheable m p ∧ input.flag = .eof ∧ key = cacheKey m p env input ∧
      m.denotes p input fs env memo.result

/-- The local filesystem named in `lem:paper-cache-reuse` and
`lem:paper-hit-completion` fixes only the `def:paper-cache-wf` filesystem.
The historical probe, environment, and input remain existential. -/
def EntryWitness (m : CommandModel sig) (key : Key sig) (memo : Memo sig)
    (fs : FS sig) : Prop :=
  ∃ p env input,
    Cacheable m p ∧ input.flag = .eof ∧ key = cacheKey m p env input ∧
    m.denotes p input fs env memo.result

/-- Explicit `def:paper-cache-wf` choices for the `def:paper-timestamps`
specified caches and fixed initial witnesses.
The selected input/filesystem retain the historical probe/environment certificate.
This predicate adds no timestamp consistency between those choices. -/
def WitnessesFor (m : CommandModel sig) (cache : Cache sig)
    (witnesses : WitnessMap sig) : Prop :=
  FMap.dom witnesses = FMap.dom cache ∧
    ∀ key memo, FMap.get cache key = some memo →
      ∃ witness, FMap.get witnesses key = some witness ∧
        ∃ p env, Cacheable m p ∧ witness.input.flag = .eof ∧
          key = cacheKey m p env witness.input ∧
          m.denotes p witness.input witness.fs env memo.result

end

end Incr
