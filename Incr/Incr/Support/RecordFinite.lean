import Incr.Incr.Semantics.Execution

/-!
# Finiteness of canonical whole-map record inventories

Finiteness is derived from finite worlds and finite recorded traces. It is not
an additional execution premise.
-/

open Incr
namespace Incr.Incr

noncomputable section

variable {sig : Signature} {m : CommandModel sig} {h : Host sig}
  {executor : Executor} {prog : sig.Prog} {start : World sig}

theorem cachePaperRecords_finite (cache : Cache sig) : (cachePaperRecords cache).Finite := by
  apply (List.finite_toSet (cache.entries.toList.map fun kv => kv.2.patch)).subset
  rintro record ⟨key, memo, present, rfl⟩
  exact List.mem_map.mpr ⟨⟨key, memo⟩, Multiset.mem_toList.mpr (Finmap.lookup_eq_some_iff.mp present), rfl⟩

theorem witnessPaperRecords_finite (witnesses : WitnessMap sig) : (witnessPaperRecords witnesses).Finite := by
  apply (List.finite_toSet (witnesses.entries.toList.map fun kv => recordOfFS kv.2.fs)).subset
  rintro record ⟨key, witness, present, rfl⟩
  exact List.mem_map.mpr ⟨⟨key, witness⟩, Multiset.mem_toList.mpr (Finmap.lookup_eq_some_iff.mp present), rfl⟩

theorem worldPaperRecords_finite (world : World sig) : (worldPaperRecords world).Finite := by
  have sandboxFinite : {record : RecordMap sig | ∃ slot sb,
      FMap.get world.sandbox slot = some sb ∧
      (record = recordOfFS sb.base ∨ record = sb.patch ∨ record = recordOfFS sb.view)}.Finite := by
    apply (List.finite_toSet (world.sandbox.entries.toList.flatMap fun kv =>
      [recordOfFS kv.2.base, kv.2.patch, recordOfFS kv.2.view])).subset
    rintro record ⟨slot, sb, present, cases⟩
    apply List.mem_flatMap.mpr
    refine ⟨⟨slot, sb⟩, Multiset.mem_toList.mpr (Finmap.lookup_eq_some_iff.mp present), ?_⟩
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using cases
  exact ((Set.finite_singleton _).union (cachePaperRecords_finite world.cache)).union sandboxFinite

theorem StepDerivation.callPaperRecords_finite (d : StepDerivation m h executor prog) :
    d.callPaperRecords.Finite := by
  cases call : ProbeDerivation.callFS d.probe with
  | none => simp [StepDerivation.callPaperRecords, call]
  | some fs =>
    apply (Set.finite_singleton (recordOfFS fs)).subset
    rintro record ⟨other, same, rfl⟩
    rw [call] at same
    cases Option.some.inj same
    rfl

theorem StepDerivation.applicationPaperRecords_finite (d : StepDerivation m h executor prog) :
    d.applicationPaperRecords.Finite := by
  have sandbox : {record : RecordMap sig | ∃ fs, d.sandboxApplication = some fs ∧
      record = recordOfFS fs}.Finite := by
    cases chosen : d.sandboxApplication with
    | none => simp
    | some fs =>
      apply (Set.finite_singleton (recordOfFS fs)).subset
      rintro record ⟨other, same, rfl⟩
      cases Option.some.inj same
      rfl
  have commit : {record : RecordMap sig | ∃ patch, d.livePatch = some patch ∧
      record = recordOfFS (applyPatch d.selected.fs patch)}.Finite := by
    cases chosen : d.livePatch with
    | none => simp
    | some patch =>
      apply (Set.finite_singleton (recordOfFS (applyPatch d.selected.fs patch))).subset
      rintro record ⟨other, same, rfl⟩
      cases Option.some.inj same
      rfl
  exact sandbox.union commit

theorem StepDerivation.paperRecords_finite (d : StepDerivation m h executor prog) :
    d.paperRecords.Finite := by
  exact (((((worldPaperRecords_finite d.before).union (worldPaperRecords_finite d.selected)).union
    (worldPaperRecords_finite d.after)).union (Set.finite_singleton _)).union
    d.callPaperRecords_finite).union d.applicationPaperRecords_finite

theorem finite_stepPaperRecords (trace : Trace m h executor prog) :
    {record : RecordMap sig | ∃ d ∈ trace, record ∈ d.paperRecords}.Finite := by
  induction trace with
  | nil => simp
  | cons d rest ih =>
    have eq : {record : RecordMap sig | ∃ e ∈ d :: rest, record ∈ e.paperRecords} =
        d.paperRecords ∪ {record | ∃ e ∈ rest, record ∈ e.paperRecords} := by
      ext record
      simp only [Set.mem_ofPred_eq, Set.mem_union, List.mem_cons]
      constructor
      · rintro ⟨e, rfl | member, recorded⟩
        · exact Or.inl recorded
        · exact Or.inr ⟨e, member, recorded⟩
      · rintro (member | ⟨e, inRest, recorded⟩)
        · exact ⟨d, Or.inl rfl, member⟩
        · exact ⟨e, Or.inr inRest, recorded⟩
    rw [eq]
    exact d.paperRecords_finite.union ih

theorem Prefix.paperRecords_finite (pre : Prefix m h executor prog start) : pre.paperRecords.Finite :=
  (worldPaperRecords_finite start).union (finite_stepPaperRecords pre.trace)

theorem Prefix.selectedPaperRecords_finite (pre : Prefix m h executor prog start) (selected : World sig) :
    (pre.selectedPaperRecords selected).Finite :=
  pre.paperRecords_finite.union (worldPaperRecords_finite selected)

end
end Incr.Incr
