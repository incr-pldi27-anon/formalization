import Incr.Incr.Reuse.Validation
import Incr.Incr.Math.PatchAlgebra
import Incr.Incr.Reuse.Boundary
import Incr.Incr.Preservation.Proof

/-! # `lem:paper-hit-completion`: semantic completion and named cache-hit
enabledness -/

open Incr
namespace Incr.Incr

noncomputable section

variable {sig : Signature} {m : CommandModel sig}

/-- A restricted merge retains every new dependency outside the staged patch. -/
theorem hit_dependency_bound {V : Type} (old next total : FMap sig.Path V)
    (patch : Patch sig)
    (eqn : old ⊎ (next ↾ (Set.univ \ FMap.dom patch)) = total) :
    FMap.dom next ⊆ FMap.dom total ∪ FMap.dom patch := by
  classical
  intro q hq
  by_cases hp : q ∈ FMap.dom patch
  · exact Or.inr hp
  · apply Or.inl
    rw [← eqn, FMap.dom_merge]
    apply Or.inr
    obtain ⟨v, hv⟩ := Finmap.mem_iff.mp (Finmap.mem_keys.mp hq)
    apply Finmap.mem_keys.mpr
    apply Finmap.mem_iff.mpr
    exact ⟨v, (FMap.get_restrict_eq_some _ _ _ _).mpr ⟨⟨Set.mem_univ q, hp⟩, hv⟩⟩

theorem hit_restrict_eq_filter {V : Type} (next : FMap sig.Path V) (patch : Patch sig) :
    next ↾ (Set.univ \ FMap.dom patch) =
      FMap.filterKeys (fun q => q ∉ FMap.keys patch) next := by
  classical
  apply Finmap.ext_lookup
  intro q
  change FMap.get _ q = FMap.get _ q
  rw [FMap.get_restrict, FMap.get_filterKeys]
  by_cases hq : q ∈ FMap.keys patch <;> simp [FMap.dom, FMap.keys] at hq ⊢ <;> simp [hq]

/-- Compare a fresh closing call's folded result with the memo. -/
theorem hit_completion_of_fold
    (shape : DenotationShape m) (commands : WellFormedCommands m)
    (p : sig.Probe) (env : Env sig) (sb : Sandbox sig) (s : Bytes)
    (memo : Memo sig) (hi : sb.input.flag = .open) (ho : sb.output.flag = .open)
    (whole : ∀ result, m.denotes p (Chunk.concat sb.input ⟨s, .eof⟩ hi) sb.base env result →
      ResultEquivalent memo.result result)
    (closing : ∃ result, m.denotes p ⟨s, .eof⟩ sb.view env result)
    (fold : ∀ result, m.denotes p ⟨s, .eof⟩ sb.view env result →
      m.denotes p (Chunk.concat sb.input ⟨s, .eof⟩ hi) sb.base env
        (combineResults (sandboxResult sb) result ho))
    (forbidden : Set sig.MTime) (finite : forbidden.Finite) :
    CacheHitCompletion m p env sb s memo ho forbidden := by
  classical
  obtain ⟨r, hr⟩ := closing
  obtain ⟨patch, approx, fresh⟩ := commands.timestamps.fresh forbidden finite r.patch
  let result : Result sig := { r with patch := patch }
  have denotes : m.denotes p ⟨s, .eof⟩ sb.view env result :=
    commands.timestamps.retimestamp p _ _ _ r hr patch approx
  have eqv := whole _ (fold result denotes)
  have fields := eqv.1
  have hs : result.status = some memo.ec := congrArg (fun x => x.1) fields
  have hrds : sb.reads ⊎ (result.reads ↾ (Set.univ \ FMap.dom sb.patch)) = memo.reads := by
    have he := congrArg (fun x => x.2.1) fields
    dsimp [combineResults, sandboxResult, Memo.result] at he
    rw [hit_restrict_eq_filter]
    exact he
  have hwrs : sb.writes ⊎ (result.writes ↾ (Set.univ \ FMap.dom sb.patch)) = memo.writes := by
    have he := congrArg (fun x => x.2.2.1) fields
    dsimp [combineResults, sandboxResult, Memo.result] at he
    rw [hit_restrict_eq_filter]
    exact he
  have hout : memo.output = sb.output ++'ho result.output :=
    (congrArg (fun x => x.2.2.2) fields).symm
  refine ⟨result, denotes, hs, (shape p _ _ _ result denotes).2 rfl |>.1,
    hout, eqv.2, hrds, hwrs, fresh, ?_, ?_⟩
  · exact (FMap.dom_merge sb.patch result.patch).symm.trans eqv.2.1
  · have rd := hit_dependency_bound sb.reads result.reads memo.reads sb.patch hrds
    have wr := hit_dependency_bound sb.writes result.writes memo.writes sb.patch hwrs
    intro q hq
    rcases hq with hq | hq
    · rcases rd hq with hq | hq
      · exact Or.inl (Or.inl hq)
      · exact Or.inr hq
    · rcases wr hq with hq | hq
      · exact Or.inl (Or.inr hq)
      · exact Or.inr hq

/-- `asm:paper-continuation` supplies the closing call once `lem:paper-sandbox`
supplies the actual prefix denotation. -/
theorem hit_completion_progressed
    (shape : DenotationShape m) (commands : WellFormedCommands m)
    (p : sig.Probe) (env : Env sig) (sb : Sandbox sig) (s : Bytes)
    (memo : Memo sig) (hi : sb.input.flag = .open) (ho : sb.output.flag = .open)
    (cacheable : Cacheable m p)
    (prefixDenotes : m.denotes p sb.input sb.base env (sandboxResult sb))
    (witnessFS : FS sig)
    (reuse : CacheReuseResult m p env (Chunk.concat sb.input ⟨s, .eof⟩ hi) memo witnessFS sb.base)
    (forbidden : Set sig.MTime) (finite : forbidden.Finite) :
    CacheHitCompletion m p env sb s memo ho forbidden := by
  apply hit_completion_of_fold shape commands p env sb s memo hi ho reuse.2.2
  · exact commands.completion p cacheable env sb.base sb.input s
      (sandboxResult sb) memo.result hi rfl ho memo.output_eof prefixDenotes reuse.2.1
  · intro result denotes
    exact commands.chunk p cacheable env sb.base sb.input ⟨s, .eof⟩
      (sandboxResult sb) result hi rfl ho prefixDenotes denotes
  · exact finite

/-- An initialized sandbox leaves the remaining call and its result unchanged. -/
theorem hit_initial_fold (base : FS sig) (result : Result sig)
    (ho : (Sandbox.initial base).output.flag = .open) :
    combineResults (sandboxResult (Sandbox.initial base)) result ho = result := by
  cases result
  dsimp [combineResults, sandboxResult, Sandbox.initial, Chunk.emptyOpen, Chunk.concat]
  simp only [FMap.filterKeys_keys_empty, FMap.merge_empty_earlier]

/-- With no preceding open step, `lem:paper-cache-reuse` already supplies the
remaining call. -/
theorem hit_completion_initial
    (shape : DenotationShape m) (commands : WellFormedCommands m)
    (p : sig.Probe) (env : Env sig) (base : FS sig) (s : Bytes) (memo : Memo sig)
    (witnessFS : FS sig)
    (reuse : CacheReuseResult m p env ⟨s, .eof⟩ memo witnessFS base)
    (forbidden : Set sig.MTime) (finite : forbidden.Finite) :
    CacheHitCompletion m p env (Sandbox.initial base) s memo rfl forbidden := by
  apply hit_completion_of_fold shape commands p env (Sandbox.initial base) s memo rfl rfl
  · simpa only [Sandbox.initial, Chunk.emptyOpen, Chunk.concat, List.nil_append]
      using reuse.2.2
  · exact ⟨memo.result, by simpa only [Sandbox.view, Sandbox.initial, applyPatch_empty]
      using reuse.2.1⟩
  · intro result denotes
    have hresult := hit_initial_fold base result rfl
    have hdenotes : m.denotes p ⟨s, .eof⟩ base env result := by
      simpa only [Sandbox.view, Sandbox.initial, applyPatch_empty] using denotes
    exact hresult.symm ▸ hdenotes
  · exact finite

/-- `lem:paper-cache-reuse` and the two `lem:paper-sandbox` cases imply every
semantic clause of `lem:paper-hit-completion`. -/
theorem hit_completion_from_witness
    (shape : DenotationShape m) (commands : WellFormedCommands m)
    (key : HashInjective m) (cache : Cache sig) (cacheWF : WellFormedCache m cache)
    (p : sig.Probe) (env : Env sig) (sb : Sandbox sig) (s : Bytes)
    (memo : Memo sig) (hi : sb.input.flag = .open) (ho : sb.output.flag = .open)
    (cacheable : Cacheable m p)
    (entry : FMap.get cache (cacheKey m p env (Chunk.concat sb.input ⟨s, .eof⟩ hi)) = some memo)
    (witnessFS : FS sig)
    (witness : EntryWitness m (cacheKey m p env (Chunk.concat sb.input ⟨s, .eof⟩ hi)) memo witnessFS)
    (valid : Valid m memo.reads memo.writes sb.base)
    (timestamps : TimestampConsistent ({recordOfFS witnessFS} ∪ {recordOfFS sb.base}))
    (cases : sb = Sandbox.initial sb.base ∨
      m.denotes p sb.input sb.base env (sandboxResult sb))
    (forbidden : Set sig.MTime) (finite : forbidden.Finite) :
    CacheHitCompletion m p env sb s memo ho forbidden := by
  have reuse := validation_and_cache_reuse shape commands key cache cacheWF p env
    (Chunk.concat sb.input ⟨s, .eof⟩ hi) memo witnessFS sb.base rfl entry witness valid timestamps
  rcases cases with initial | progressed
  · have bytes : sb.input.bytes = [] := congrArg (fun x => x.input.bytes) initial
    have inputEq : Chunk.concat sb.input ⟨s, .eof⟩ hi = ⟨s, .eof⟩ := by
      simp only [Chunk.concat, bytes, List.nil_append]
    have reuse0 : CacheReuseResult m p env ⟨s, .eof⟩ memo witnessFS sb.base :=
      inputEq ▸ reuse
    have done := hit_completion_initial shape commands p env sb.base s memo witnessFS
      reuse0 forbidden finite
    simpa only [← initial] using done
  · exact hit_completion_progressed shape commands p env sb s memo hi ho cacheable
      progressed witnessFS reuse forbidden finite

/-- Routing exists for the actual consumed map when any present successor is open. -/
theorem hit_routing_exists (buffers : FMap Nat Chunk) (i : Nat) (output : Chunk)
    (ready : ∀ next, FMap.get buffers (i + 1) = some next → next.flag = .open) :
    ∃ routed out, put (buffers ∖ i) i output = some (routed, out) := by
  have ne : i + 1 ≠ i := by omega
  unfold put
  rw [FMap.get_erase_of_ne ne]
  cases hn : FMap.get buffers (i + 1) with
  | none => exact ⟨_, _, rfl⟩
  | some next =>
    have hf := ready next hn
    cases next with
    | mk bytes flag =>
      dsimp at hf
      subst flag
      exact ⟨_, _, rfl⟩

/-- The completion output and actual routing map enable the named hit rule. -/
theorem hit_application_of_completion
    (selected : World sig) (p : sig.Probe) (i : Nat) (sb : Sandbox sig) (s : Bytes)
    (memo : Memo sig) (hi : sb.input.flag = .open) (ho : sb.output.flag = .open)
    (cacheable : Cacheable m p)
    (buffer : FMap.get selected.buffer i = some ⟨s, .eof⟩)
    (sandbox : FMap.get selected.sandbox i = some sb)
    (entry : FMap.get selected.cache
      (cacheKey m p selected.env (Chunk.concat sb.input ⟨s, .eof⟩ hi)) = some memo)
    (order : BufferOrder selected.buffer)
    (forbidden : Set sig.MTime)
    (completion : CacheHitCompletion m p selected.env sb s memo ho forbidden)
    (valid : Valid m memo.reads memo.writes selected.fs) :
    Nonempty (CacheCloseHitApplication m selected p i sb s memo) := by
  obtain ⟨closing, _, _, eof, guard, _⟩ := completion
  obtain ⟨buffers, out, routing⟩ := hit_routing_exists selected.buffer i
    ⟨closing.output.bytes, .eof⟩ (fun next hn => order i _ next buffer hn)
  have output : closing.output = ⟨closing.output.bytes, .eof⟩ := by
    cases he : closing.output with
    | mk bytes flag =>
      have hf : flag = .eof := by simpa only [he] using eof
      subst flag
      rfl
  exact ⟨⟨closing.output.bytes, buffers, out, hi, ho, cacheable, buffer,
    sandbox, entry, valid, by rw [← output]; exact guard, routing⟩⟩

variable {h : Host sig} {prog : sig.Prog} {start : World sig}

/-- `lem:paper-hit-completion` (cache-hit completion): all completion clauses and
named `Cache-Close-Hit` enabledness. Open flags are local definitions derived
from reachability and H1, not caller hypotheses. The witness is local to this
memo. -/
theorem cache_hit_completion (_shape : DenotationShape m)
    (_commands : WellFormedCommands m) (_key : HashInjective m)
    (host : HostWellFormed m h) (_cache : WellFormedCache m start.cache)
    (pre : Prefix m h .incr prog start) (operational : Operational pre)
    (selection : Selection sig) (selected : World sig)
    (selectedByHost : h.select prog pre.final selection selected)
    (p : sig.Probe) (i : Nat) (sb : Sandbox sig) (s : Bytes) (memo : Memo sig)
    (_head : selection.head = .pipeline p i)
    (sandbox : FMap.get selected.sandbox i = some sb)
    (_buffer : FMap.get selected.buffer i = some ⟨s, .eof⟩)
    (_cacheable : Cacheable m p) :
    let flags := operational.selectedOpenSandboxes host selectedByHost i sb sandbox
    ∀ (_entry : FMap.get selected.cache
        (cacheKey m p selected.env (sb.input ++'(flags.1) ⟨s, .eof⟩)) = some memo)
      (witnessFS : FS sig)
      (_witness : EntryWitness m
        (cacheKey m p selected.env (sb.input ++'(flags.1) ⟨s, .eof⟩)) memo witnessFS)
      (_validBase : Valid m memo.reads memo.writes sb.base)
      (_timestamps : TimestampConsistent ({recordOfFS witnessFS} ∪ {recordOfFS sb.base}))
      (forbidden : Set sig.MTime) (_finite : forbidden.Finite),
    CacheHitCompletion m p selected.env sb s memo flags.2 forbidden ∧
      (Valid m memo.reads memo.writes selected.fs →
        Nonempty (CacheCloseHitApplication m selected p i sb s memo)) := by
  dsimp only
  intro entry witnessFS witness validBase timestamps forbidden finite
  have hd := host.selectionDiscipline .incr prog start pre operational selection selected selectedByHost
  have preserved := cacheable_prefixes _shape _commands _key host _cache pre operational
  have state := (buffer_sandbox_preservation _shape _commands _key host pre operational).1
  have cases := hit_selected_prefix_cases operational host state preserved.2.1
    selectedByHost _head sandbox _cacheable
  have selectedCache : WellFormedCache m selected.cache := by
    rw [hd.2.2.1]
    exact preserved.1
  let flags := operational.selectedOpenSandboxes host selectedByHost i sb sandbox
  have completion := hit_completion_from_witness _shape _commands _key selected.cache
    selectedCache p selected.env sb s memo flags.1 flags.2 _cacheable entry witnessFS witness
    validBase timestamps cases forbidden finite
  refine ⟨completion, ?_⟩
  intro validLive
  have order := hd.bufferOrder
    (host.inputDelivery .incr prog start pre operational selection selected selectedByHost)
    (operational.bufferOrder host)
  exact hit_application_of_completion selected p i sb s memo flags.1 flags.2 _cacheable
    _buffer sandbox entry order forbidden completion validLive

end
end Incr.Incr
