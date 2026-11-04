import Incr.Foundation.Data

/-!
# Dependencies, records, and timestamp consistency

Read and write dependency maps, dependency agreement
(`def:model-dependency-agreement`), the flattened record representation used
by the timestamp proof, timestamp consistency (`def:paper-timestamps`), and
the freshness side condition on executing calls.
-/

namespace Incr

noncomputable section

/-- `def:model-dependency-agreement`: exact read entries, but only write-target contents. -/
def DepAgree {sig : Signature} (r : Reads sig) (w : Writes sig)
    (fs fs' : FS sig) : Prop :=
  FMap.dom r ∪ FMap.dom w ⊆ FMap.dom fs ∩ FMap.dom fs' ∧
  (∀ q ∈ FMap.dom r, FMap.get fs q = FMap.get fs' q) ∧
  (∀ q ∈ FMap.dom w,
    (FMap.get fs q).map File.content = (FMap.get fs' q).map File.content)

/-- `fs ≅[R,W] fs'` — paper dependency agreement
(`def:model-dependency-agreement`, appendix.tex:155): exact agreement on read
paths, content agreement on write paths, and both domains cover the recorded
paths. -/
notation:50 fs:51 " ≅[" R:max ", " W:max "] " fs':50 => DepAgree R W fs fs'


/-- Flattened file records retain their paths for timestamp comparison.
This ghost helper enumerates the map, so it stays `noncomputable`. -/
abbrev Records (sig : Signature) := List (sig.Path × File sig)

noncomputable def fsRecords {sig : Signature} (fs : FS sig) : Records sig :=
  fs.entries.toList.map fun kv => (kv.1, kv.2)

theorem get_of_mem_fsRecords {sig : Signature} {fs : FS sig} {q : sig.Path} {f : File sig}
    (h : (q, f) ∈ fsRecords fs) : FMap.get fs q = some f := by
  unfold fsRecords at h
  rw [List.mem_map] at h
  obtain ⟨kv, hkv, hpair⟩ := h
  obtain ⟨a, b⟩ := kv
  simp only [Prod.mk.injEq] at hpair
  obtain ⟨h1, h2⟩ := hpair
  subst h1
  subst h2
  exact Finmap.lookup_eq_some_iff.mpr (Multiset.mem_toList.mp hkv)

theorem mem_fsRecords_of_get {sig : Signature} {fs : FS sig} {q : sig.Path} {f : File sig}
    (h : FMap.get fs q = some f) : (q, f) ∈ fsRecords fs := by
  unfold fsRecords
  rw [List.mem_map]
  exact ⟨⟨q, f⟩, Multiset.mem_toList.mpr (Finmap.lookup_eq_some_iff.mp h), rfl⟩

noncomputable def patchRecords {sig : Signature} (patch : Patch sig) : Records sig :=
  patch.entries.toList.filterMap fun kv =>
    match kv.2 with
    | .write f => some (kv.1, f)
    | .delete => none

/-- `def:paper-timestamps`: equal timestamps at the same path imply equal contents. -/
def TimestampCompatible {sig : Signature} (records : Records sig) : Prop :=
  ∀ q f f', (q, f) ∈ records → (q, f') ∈ records →
    f.mtime = f'.mtime → f.content = f'.content

/-- Timestamp compatibility is inherited by sublists of records. -/
theorem TimestampCompatible.mono {sig : Signature} {r r' : Records sig}
    (hsub : ∀ x ∈ r, x ∈ r') (h : TimestampCompatible r') : TimestampCompatible r :=
  fun q f f' hf hf' hm => h q f f' (hsub _ hf) (hsub _ hf') hm

/-- Local freshness concerns both the call filesystem and the live filesystem.
This is the timestamp side condition of `sec:model-probe` (`model.tex`):
"Whenever a probe rule executes a command, each file created or overwritten in
the newly returned patch must have a timestamp absent from both the command's
filesystem argument and the live filesystem; deletion markers need no
timestamp."

The paper attaches this condition to the rule figures as a shared note
("Timestamp side conditions are as in `sec:model-probe`") instead of writing
it in the rule equations; `Executes` fuses it into the call premise so each
rule carries it explicitly. Replayed patches keep their recorded timestamps
("Applying accumulated or cached patches preserves their recorded
timestamps"), so the condition applies to `Executes` only, not `Action.replay`. -/
def FreshPatch {sig : Signature} (d : Patch sig) (callFS liveFS : FS sig) : Prop :=
  ∀ q f, FMap.get d q = some (.write f) →
    ∀ q' old, (FMap.get callFS q' = some old ∨ FMap.get liveFS q' = some old) →
      f.mtime ≠ old.mtime

end

end Incr
