import Incr.Foundation.Deps

/-!
# Whole-map record collections (paper `def:paper-timestamps`)

The public predicate retains map membership and the two printed lookups.
File occurrences are derived proof support, not a replacement collection.
RC1 in `docs/record-collection-semantics.md` fixes the operational inventories.
-/

namespace Incr

noncomputable section

/-- A recorded map has the paper's common file-or-delete codomain. -/
abbrev RecordMap (sig : Signature) := Patch sig

/-- Whole-map membership, without an event order or an extra role tag. -/
abbrev RecordCollection (sig : Signature) := Set (RecordMap sig)

/-- Embed every filesystem entry, preserving the whole map and its timestamps. -/
def recordOfFS {sig : Signature} (fs : FS sig) : RecordMap sig :=
  FMap.filterMap (fun _ file => some (.write file)) fs

/-- `def:paper-timestamps` (timestamp consistency): two recorded maps with the
same path and timestamp agree in contents. -/
def TimestampConsistent {sig : Signature} (records : RecordCollection sig) : Prop :=
  ∀ m ∈ records, ∀ m' ∈ records,
    ∀ (q : sig.Path) (c c' : sig.Content) (t : sig.MTime),
      (FMap.get m q = some (.write ⟨c, t⟩) ∧
       FMap.get m' q = some (.write ⟨c', t⟩)) → c = c'

/-- Derived file occurrences forget map boundaries only inside proof support. -/
def recordOccurrences {sig : Signature} (records : RecordCollection sig) : Set (sig.Path × File sig) :=
  {entry | ∃ m ∈ records, FMap.get m entry.1 = some (.write entry.2)}

variable {sig : Signature}

@[simp] theorem get_recordOfFS (fs : FS sig) (q : sig.Path) :
    FMap.get (recordOfFS fs) q = (FMap.get fs q).map Edit.write := by
  rw [recordOfFS, FMap.get_filterMap]
  cases FMap.get fs q <;> rfl

@[simp] theorem dom_recordOfFS (fs : FS sig) : FMap.dom (recordOfFS fs) = FMap.dom fs := by
  ext q
  change q ∈ (recordOfFS fs).keys ↔ q ∈ fs.keys
  rw [FMap.mem_keys_iff, FMap.mem_keys_iff]
  apply not_iff_not.mp
  rw [← FMap.get_eq_none, ← FMap.get_eq_none, get_recordOfFS]
  simp

theorem recordOfFS_injective : Function.Injective (recordOfFS (sig := sig)) := by
  intro left right same
  apply Finmap.ext_lookup
  intro q
  change FMap.get left q = FMap.get right q
  have lookup := congrArg (fun m => FMap.get m q) same
  rw [get_recordOfFS, get_recordOfFS] at lookup
  cases hl : FMap.get left q <;> cases hr : FMap.get right q <;> simp_all

@[simp] theorem recordOfFS_empty : recordOfFS (∅ : FS sig) = ∅ := by
  apply Finmap.ext_lookup
  intro q
  change FMap.get (recordOfFS ∅) q = FMap.get ∅ q
  rw [get_recordOfFS]
  simp [FMap.get]

theorem recordOccurrences_mono {records records' : RecordCollection sig}
    (subset : records ⊆ records') : recordOccurrences records ⊆ recordOccurrences records' := by
  rintro entry ⟨m, member, lookup⟩
  exact ⟨m, subset member, lookup⟩

@[simp] theorem recordOccurrences_empty : recordOccurrences (∅ : RecordCollection sig) = ∅ := by
  ext entry
  simp [recordOccurrences]

@[simp] theorem recordOccurrences_union (left right : RecordCollection sig) :
    recordOccurrences (left ∪ right) = recordOccurrences left ∪ recordOccurrences right := by
  ext entry
  simp only [recordOccurrences, Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · rintro ⟨m, leftOrRight, lookup⟩
    rcases leftOrRight with member | member
    · exact Or.inl ⟨m, member, lookup⟩
    · exact Or.inr ⟨m, member, lookup⟩
  · rintro (⟨m, member, lookup⟩ | ⟨m, member, lookup⟩)
    · exact ⟨m, Or.inl member, lookup⟩
    · exact ⟨m, Or.inr member, lookup⟩

@[simp] theorem mem_recordOccurrences_fs (fs : FS sig) (q : sig.Path) (file : File sig) :
    (q, file) ∈ recordOccurrences {recordOfFS fs} ↔ FMap.get fs q = some file := by
  cases lookup : FMap.get fs q <;> simp [recordOccurrences, lookup]

@[simp] theorem mem_recordOccurrences_patch (patch : Patch sig) (q : sig.Path) (file : File sig) :
    (q, file) ∈ recordOccurrences {patch} ↔ FMap.get patch q = some (.write file) := by
  simp [recordOccurrences]

/-- The old finite file list describes occurrences, not whole-map membership. -/
theorem mem_patchRecords_iff_lookup (patch : Patch sig) (q : sig.Path) (file : File sig) :
    (q, file) ∈ patchRecords patch ↔ FMap.get patch q = some (.write file) := by
  constructor
  · intro member
    unfold patchRecords at member
    obtain ⟨entry, inEntries, mapped⟩ := List.mem_filterMap.mp member
    rcases entry with ⟨path, edit⟩
    cases edit with
    | delete => simp at mapped
    | write written =>
      simp only [Option.some.injEq, Prod.mk.injEq] at mapped
      obtain ⟨rfl, rfl⟩ := mapped
      exact Finmap.lookup_eq_some_iff.mpr (Multiset.mem_toList.mp inEntries)
  · intro lookup
    exact List.mem_filterMap.mpr ⟨⟨q, .write file⟩,
      Multiset.mem_toList.mpr (Finmap.lookup_eq_some_iff.mp lookup), rfl⟩

theorem mem_recordOccurrences_fs_iff_mem_fsRecords (fs : FS sig) (q : sig.Path) (file : File sig) :
    (q, file) ∈ recordOccurrences {recordOfFS fs} ↔ (q, file) ∈ fsRecords fs := by
  rw [mem_recordOccurrences_fs]
  exact ⟨mem_fsRecords_of_get, get_of_mem_fsRecords⟩

theorem TimestampConsistent.mono {records records' : RecordCollection sig}
    (subset : records ⊆ records') (consistent : TimestampConsistent records') : TimestampConsistent records := by
  intro m member m' member' q c c' t lookups
  exact consistent m (subset member) m' (subset member') q c c' t lookups

@[simp] theorem TimestampConsistent.empty : TimestampConsistent (∅ : RecordCollection sig) := by
  simp [TimestampConsistent]

/-- A single map has only one file value at each path. -/
theorem TimestampConsistent.singleton (m : RecordMap sig) : TimestampConsistent {m} := by
  intro left member right member' q c c' t lookups
  have leftEq := Set.mem_singleton_iff.mp member
  have rightEq := Set.mem_singleton_iff.mp member'
  subst left
  subst right
  have files := Edit.write.inj (Option.some.inj (lookups.1.symm.trans lookups.2))
  exact congrArg File.content files

/-- This equivalence supports proofs; the public definition keeps map binders. -/
theorem timestampConsistent_iff_occurrences (records : RecordCollection sig) :
    TimestampConsistent records ↔
      ∀ q f f', (q, f) ∈ recordOccurrences records → (q, f') ∈ recordOccurrences records →
        f.mtime = f'.mtime → f.content = f'.content := by
  constructor
  · intro consistent q f f' first second time
    obtain ⟨m, member, lookup⟩ := first
    obtain ⟨m', member', lookup'⟩ := second
    rcases f with ⟨c, t⟩
    rcases f' with ⟨c', t'⟩
    dsimp only at time ⊢
    cases time
    exact consistent m member m' member' q c c' t ⟨lookup, lookup'⟩
  · intro consistent m member m' member' q c c' t lookups
    exact consistent q ⟨c, t⟩ ⟨c', t⟩ ⟨m, member, lookups.1⟩ ⟨m', member', lookups.2⟩ rfl

/-- An existing finite list can be reused only after its exact occurrence bridge. -/
theorem timestampConsistent_iff_normalized (records : RecordCollection sig) (files : Records sig)
    (occurrences : ∀ q f, (q, f) ∈ recordOccurrences records ↔ (q, f) ∈ files) :
    TimestampConsistent records ↔ TimestampCompatible files := by
  rw [timestampConsistent_iff_occurrences]
  constructor
  · intro consistent q f f' first second time
    exact consistent q f f' ((occurrences q f).mpr first) ((occurrences q f').mpr second) time
  · intro consistent q f f' first second time
    exact consistent q f f' ((occurrences q f).mp first) ((occurrences q f').mp second) time

/-- Finite map enumerations can normalize proof data without changing the public predicate. -/
theorem timestampConsistent_list_iff (maps : List (RecordMap sig)) :
    TimestampConsistent {m | m ∈ maps} ↔ TimestampCompatible (maps.flatMap patchRecords) := by
  apply timestampConsistent_iff_normalized
  intro q file
  constructor
  · rintro ⟨m, member, lookup⟩
    exact List.mem_flatMap.mpr ⟨m, member, (mem_patchRecords_iff_lookup m q file).mpr lookup⟩
  · intro member
    obtain ⟨m, inMaps, recorded⟩ := List.mem_flatMap.mp member
    exact ⟨m, inMaps, (mem_patchRecords_iff_lookup m q file).mp recorded⟩

end
end Incr
