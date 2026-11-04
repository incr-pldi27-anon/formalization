import Incr.IncrPP.Bisimulation.Proof

/-!
# Lifting the named bisimulation to finite live runs

Every source prefix keeps the source run's chosen initial witnesses.
The target is separately admitted; no cross-history consistency is assumed.
-/

namespace Incr.IncrPP

noncomputable section

variable {sig : Signature} {m : CommandModel sig} {h : Host sig}
  {executor : Executor} {prog : sig.Prog} {start : World sig}

/-- Record collections grow along an actual connected trace prefix. -/
theorem Prefix.records_of_isPrefix {short long : Prefix m h executor prog start}
    (prefixTrace : short.trace.IsPrefix long.trace) : ∀ record ∈ short.records, record ∈ long.records := by
  obtain ⟨tail, joined⟩ := prefixTrace
  intro record member
  simp only [Prefix.records, List.mem_append, List.mem_flatMap] at member ⊢
  rcases member with initial | ⟨step, stepAt, recorded⟩
  · exact Or.inl initial
  · exact Or.inr ⟨step, by rw [← joined]; exact List.mem_append_left tail stepAt, recorded⟩

/-- A separately admitted prefix remains admitted with the same fixed witnesses when shortened. -/
theorem Admissible.of_trace_isPrefix {witnesses : WitnessMap sig}
    {short long : Prefix m h executor prog start} (admissible : Admissible witnesses long)
    (prefixTrace : short.trace.IsPrefix long.trace) : Admissible witnesses short := by
  refine ⟨admissible.operational.of_trace_isPrefix prefixTrace,
    ExitOrdered.of_trace_isPrefix admissible.ordered prefixTrace, ?_⟩
  apply (short.paperRecords_witness_consistent_iff witnesses).mpr
  apply TimestampCompatible.mono ?_ admissible.normalizedWitnesses
  intro record member
  rcases List.mem_append.mp member with old | fixed
  · exact List.mem_append_left _ (Prefix.records_of_isPrefix prefixTrace record old)
  · exact List.mem_append_right _ fixed

/-- The admitted prefix's consistency includes the initial world and fixed initial witnesses. -/
theorem Admissible.initial_consistent {witnesses : WitnessMap sig}
    {pre : Prefix m h executor prog start} (admissible : Admissible witnesses pre) :
    TimestampConsistent (worldPaperRecords start ∪ witnessPaperRecords witnesses) := by
  apply (worldPaperRecords_witness_consistent_iff start witnesses).mpr
  apply TimestampCompatible.mono ?_ admissible.normalizedWitnesses
  intro record member
  rcases List.mem_append.mp member with initial | fixed
  · exact List.mem_append_left _ (List.mem_append_left _ initial)
  · exact List.mem_append_right _ fixed

/-- A connected empty prefix is the actual zero prefix. -/
theorem Prefix.eq_zero (pre : Prefix m h executor prog start) (empty : pre.trace = [])
    (initial : Initial h prog start) : pre = zeroPrefix executor initial := by
  cases pre with
  | mk trace final preInitial connected =>
    change trace = [] at empty
    subst trace
    cases connected
    rfl

/-- Every finite admitted live prefix has a related separately admitted vanilla prefix. -/
theorem BisimulationStatement.match_live (context : PrefixContext m h prog start)
    (bisim : BisimulationStatement context) (pre : Prefix m h .live prog start)
    (admissible : Admissible context.witnesses pre) :
    ∃ target : Prefix m h .vanilla prog start, Correspondence context pre target := by
  apply Prefix.snoc_induction (fun pre => Admissible context.witnesses pre →
    ∃ target : Prefix m h .vanilla prog start, Correspondence context pre target) ?_ ?_ pre admissible
  · intro pre empty _
    refine ⟨zeroPrefix .vanilla context.initial, ?_⟩
    rw [pre.eq_zero empty context.initial]
    exact bisim.initial
  · intro short post d joined before after ih postAdmissible
    have shortAdmissible := postAdmissible.of_trace_isPrefix ⟨[d], joined.symm⟩
    obtain ⟨target, related⟩ := ih shortAdmissible
    let left : (prefixSystem .live context).State := ⟨short, shortAdmissible⟩
    let right : (prefixSystem .vanilla context).State := ⟨target, related.vanillaAdmissible⟩
    let next : (prefixSystem .live context).State := ⟨post, postAdmissible⟩
    have edge : (prefixSystem .live context).step left d.selection.head next := by
      exact ⟨shortAdmissible, postAdmissible, d, before.symm, rfl, joined, after⟩
    obtain ⟨other, _, matched⟩ := bisim.bisimulation.forward left right related d.selection.head next edge
    exact ⟨other.val, matched⟩

/-- Every finite admitted vanilla prefix has a related separately admitted live prefix. -/
theorem BisimulationStatement.match_vanilla (context : PrefixContext m h prog start)
    (bisim : BisimulationStatement context) (pre : Prefix m h .vanilla prog start)
    (admissible : Admissible context.witnesses pre) :
    ∃ target : Prefix m h .live prog start, Correspondence context target pre := by
  apply Prefix.snoc_induction (fun pre => Admissible context.witnesses pre →
    ∃ target : Prefix m h .live prog start, Correspondence context target pre) ?_ ?_ pre admissible
  · intro pre empty _
    refine ⟨zeroPrefix .live context.initial, ?_⟩
    rw [pre.eq_zero empty context.initial]
    exact bisim.initial
  · intro short post d joined before after ih postAdmissible
    have shortAdmissible := postAdmissible.of_trace_isPrefix ⟨[d], joined.symm⟩
    obtain ⟨target, related⟩ := ih shortAdmissible
    let left : (prefixSystem .live context).State := ⟨target, related.liveAdmissible⟩
    let right : (prefixSystem .vanilla context).State := ⟨short, shortAdmissible⟩
    let next : (prefixSystem .vanilla context).State := ⟨post, postAdmissible⟩
    have edge : (prefixSystem .vanilla context).step right d.selection.head next := by
      exact ⟨shortAdmissible, postAdmissible, d, before.symm, rfl, joined, after⟩
    obtain ⟨other, _, matched⟩ := bisim.bisimulation.backward left right related d.selection.head next edge
    exact ⟨other.val, matched⟩

end
end IncrPP
end Incr
