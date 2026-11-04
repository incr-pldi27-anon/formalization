import Incr.Model.Cache

/-!
# Numbered command assumptions (paper `app:command-wf`)

The shared command relation, cacheability, and validity definitions are reused.
The numbered assumptions are separate here. `def:paper-command-wf` (command
well-formedness) contains `asm:paper-deps` through `asm:paper-continuation`
only. Hash injectivity (`asm:paper-key`) and the model's result typing
discipline remain separate.
No declaration below assumes its own truth as a global axiom.
-/

namespace Incr

variable {sig : Signature}

/-- The result typing discipline of `sec:model-command`, not an extra clause
of `def:paper-command-wf` (command well-formedness). The abstract shared
`CommandModel` does not enforce it in its type. -/
def DenotationShape (m : CommandModel sig) : Prop :=
  ∀ p input fs env r, m.denotes p input fs env r →
    (input.flag = .open → r.output.flag = .open ∧ r.status = none) ∧
      (input.flag = .eof → r.output.flag = .eof ∧ ∃ es, r.status = some es)

/-- `asm:paper-deps` (dependency faithfulness): validity and transport by
recorded dependency contents. -/
structure DependencyFaithfulness (m : CommandModel sig) : Prop where
  valid : ∀ p input fs env r, m.denotes p input fs env r → Valid m r.reads r.writes fs
  transport : ∀ p input fs env r, m.denotes p input fs env r →
    ∀ fs', FSApprox (fs ↾ (FMap.dom r.reads ∪ FMap.dom r.writes))
      (fs' ↾ (FMap.dom r.reads ∪ FMap.dom r.writes)) →
      ∃ d' reads', m.denotes p input fs' env { r with patch := d', reads := reads' } ∧
        PatchApprox d' r.patch ∧ FMap.dom reads' = FMap.dom r.reads ∧
        (∀ q t, FMap.get reads' q = some t →
          ∃ f, FMap.get fs' q = some f ∧ f.mtime = t)

/-- `asm:paper-mtime` (write timestamps): fresh write timestamps exist and
results admit retimestamping. -/
structure WriteTimestamps (m : CommandModel sig) : Prop where
  fresh : ∀ (s : Set sig.MTime), s.Finite → ∀ d : Patch sig,
    ∃ d', PatchApprox d' d ∧
      ∀ q f, FMap.get d' q = some (.write f) → f.mtime ∉ s
  retimestamp : ∀ p input fs env r, m.denotes p input fs env r →
    ∀ d', PatchApprox d' r.patch → m.denotes p input fs env { r with patch := d' }

/-- `asm:paper-chunk` (chunk invariance): successive calls of a cacheable
command fold. -/
def ChunkInvariance (m : CommandModel sig) : Prop :=
  ∀ p, Cacheable m p → ∀ env fs input₁ input₂ r₁ r₂,
    (h₁ : input₁.flag = .open) → r₁.status = none → (h₃ : r₁.output.flag = .open) →
    m.denotes p input₁ fs env r₁ →
    m.denotes p input₂ (applyPatch fs r₁.patch) env r₂ →
    m.denotes p (input₁ ++'h₁ input₂) fs env (combineResults r₁ r₂ h₃)

/-- `asm:paper-continuation` (prefix completion): a progressed open prefix can
finish a complete result. -/
def PrefixCompletion (m : CommandModel sig) : Prop :=
  ∀ p, Cacheable m p → ∀ env fs inputPrefix s r₁ whole,
    (hpre : inputPrefix.flag = .open) → r₁.status = none → r₁.output.flag = .open →
    whole.output.flag = .eof →
    m.denotes p inputPrefix fs env r₁ →
    m.denotes p (inputPrefix ++'hpre ⟨s, .eof⟩) fs env whole →
    ∃ closing, m.denotes p ⟨s, .eof⟩ (applyPatch fs r₁.patch) env closing

/-- `asm:paper-key` (hash injectivity): hash injectivity is separate from
command well-formedness. O4 treats the paper's `Chunk ∪ Content` as a union of
distinct sorts, encoded
by `Sum Chunk sig.Content`. Full injectivity includes cross-sort separation.
The `lem:paper-cache-reuse` proof only uses chunk/chunk and content/content
comparisons
(`appendix.tex:762-769`). The proof does not uniquely determine the cross-sort
convention. Alternatives are in `docs/recorded-interpretation-decisions.md`. -/
def HashInjective (m : CommandModel sig) : Prop := Function.Injective m.hash

/-- `def:paper-command-wf` (command well-formedness): exactly the four numbered
command assumptions. Result typing comes from the model; `asm:paper-key` is a
separate theorem hypothesis. -/
structure WellFormedCommands (m : CommandModel sig) : Prop where
  dependencies : DependencyFaithfulness m
  timestamps : WriteTimestamps m
  chunk : ChunkInvariance m
  completion : PrefixCompletion m

end Incr
