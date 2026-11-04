import Incr.Incr.Math.PatchAlgebra
import Incr.Incr.Preservation.Components

open Incr
namespace Incr.Incr.CachePrefixes

noncomputable section

variable {sig : Signature} {m : CommandModel sig} {h : Host sig}
  {prog : sig.Prog} {start : World sig}

/-- A denoted accumulated prefix folds any next call in its historical environment. -/
theorem fold_progressed (commands : WellFormedCommands m)
    {p : sig.Probe} (cacheable : Cacheable m p) {sb : Sandbox sig} {env : Env sig}
    (hi : sb.input.flag = .open) (ho : sb.output.flag = .open)
    (denoted : m.denotes p sb.input sb.base env (sandboxResult sb))
    {input : Chunk} {result : Result sig}
    (call : m.denotes p input sb.view env result) :
    m.denotes p (sb.input ++'hi input) sb.base env
      (combineResults (sandboxResult sb) result ho) := by
  exact commands.chunk p cacheable env sb.base sb.input input (sandboxResult sb) result
    hi rfl ho denoted call

/-- Empty initialized fields make folding equal to the next call. -/
theorem fold_initial {p : sig.Probe} {fs : FS sig} {env : Env sig}
    {input : Chunk} {result : Result sig}
    (call : m.denotes p input (Sandbox.initial fs).view env result) :
    m.denotes p ((Sandbox.initial fs).input ++'(by rfl) input) fs env
      (combineResults (sandboxResult (Sandbox.initial fs)) result (by rfl)) := by
  classical
  cases input
  cases result with
  | mk status patch reads writes output =>
    cases output
    dsimp [Sandbox.initial, Sandbox.view, sandboxResult, combineResults, Chunk.concat,
      Chunk.emptyOpen] at call ⊢
    simp only [FMap.merge_empty_earlier, applyPatch_empty] at call ⊢
    rw [FMap.filterKeys_true _ _ (fun q => by simp [FMap.keys]),
      FMap.filterKeys_true _ _ (fun q => by simp [FMap.keys])]
    exact call

/-- The progressed fold clause follows from the accumulated-prefix denotation alone. -/
theorem progressed_next_call_folds (commands : WellFormedCommands m)
    {pre : Prefix m h .incr prog start} (host : HostWellFormed m h)
    (operational : Operational pre) (prefixes : CacheablePrefixes pre.trace pre.final) :
    ProgressedNextCallFolds pre host operational := by
  intro i sb k first p hs hl hf hp hc input result call
  have denoted := prefixes i sb k first hs hl hf
    (by simpa only [hp, Head.probe] using hc)
  rw [hp] at denoted
  exact fold_progressed commands hc (operational.openSandboxes host i sb hs).1
    (operational.openSandboxes host i sb hs).2 denoted call

/-- Empty accumulation has exactly the initialized sandbox fields. -/
theorem accumulation_nil {base : FS sig} {sb : Sandbox sig}
    (acc : HistoryAccumulation (m := m) (h := h) (executor := .incr)
      (prog := prog) base [] sb) : sb = Sandbox.initial base := by
  generalize he : ([] : Trace m h .incr prog) = trace at acc
  cases acc with
  | nil => rfl
  | snoc trace sb d previous hi ho hopen => simp at he

/-- The zero-open fold uses only the history part of `lem:paper-buffers`. -/
theorem zero_open_next_call_folds {trace : Trace m h .incr prog} {w : World sig}
    (state : SandboxState trace w) : ZeroOpenNextCallFolds trace w := by
  intro i sb k p env hs hl hempty _assigned _cacheable
  obtain ⟨entry, init, entryStep, latest, _at, _init, _base, acc⟩ := state.2.1 i sb hs
  have hk : k = .pipeline entry i := by
    simpa [liveComponent, latest] using hl.symm
  subst k
  change HistoryAccumulation sb.base (openHistory trace (.pipeline entry i)) sb at acc
  rw [hempty] at acc
  have hsb := accumulation_nil acc
  refine ⟨hsb, ?_⟩
  intro input result call
  have call' : m.denotes p input (Sandbox.initial sb.base).view env result := by
    simpa only [← hsb] using call
  convert fold_initial call' using 1 <;> simp only [← hsb]

/-- Once both inductive invariants are known, all next-call equations follow. -/
theorem next_call_folds (commands : WellFormedCommands m)
    {pre : Prefix m h .incr prog start} (host : HostWellFormed m h)
    (operational : Operational pre) (state : SandboxState pre.trace pre.final)
    (prefixes : CacheablePrefixes pre.trace pre.final) : NextCallFolds pre host operational :=
  ⟨progressed_next_call_folds commands host operational prefixes,
    zero_open_next_call_folds state⟩

/-- A first open step is a member of the full component history. -/
theorem first_open_mem {trace : Trace m h .incr prog} {k : Component}
    {first : StepDerivation m h .incr prog}
    (hf : (openHistory trace k).head? = some first) :
    first ∈ componentSteps trace k := by
  exact List.mem_of_mem_filter (List.mem_of_mem_head? hf)

/-- H2 gives the same head and environment for any two steps of a component. -/
theorem component_environment_uniform {trace : Trace m h .incr prog}
    (stable : ComponentEnvironments trace) {k : Component}
    {left right : StepDerivation m h .incr prog}
    (hl : left ∈ componentSteps trace k) (hr : right ∈ componentSteps trace k) :
    left.selection.head = right.selection.head ∧ left.selected.env = right.selected.env := by
  cases hh : (componentSteps trace k).head? with
  | none =>
    have hempty := List.head?_eq_none_iff.mp hh
    simp [hempty] at hl
  | some first =>
    obtain ⟨hlh, hle⟩ := stable k first hh left hl
    obtain ⟨hrh, hre⟩ := stable k first hh right hr
    exact ⟨hlh.trans hrh.symm, hle.trans hre.symm⟩

/-- A raw extension retains the earlier first open step's head and environment. -/
theorem extension_historical_fields {trace : Trace m h .incr prog}
    {d first : StepDerivation m h .incr prog} {k : Component}
    (stable : ComponentEnvironments (trace ++ [d]))
    (hf : (openHistory trace k).head? = some first)
    (component : componentAt (trace ++ [d]) trace.length d = some k) :
    d.selection.head = first.selection.head ∧ d.selected.env = first.selected.env := by
  apply component_environment_uniform stable (k := k)
  · rw [componentSteps_snoc]
    simp [component]
  · rw [componentSteps_snoc]
    exact List.mem_append_left _ (first_open_mem hf)

/-- O1 identifies the selected environment with the first open step's environment.
No operational extension or next-call freshness premise is needed. -/
theorem selected_historical_env {pre : Prefix m h .incr prog start}
    (host : HostWellFormed m h) (operational : Operational pre)
    {selection : Selection sig} {selected : World sig}
    (chosen : h.select prog pre.final selection selected)
    {p : sig.Probe} {i : Nat} {k : Component}
    {first : StepDerivation m h .incr prog}
    (noinit : selection.init = none) (head : selection.head = .pipeline p i)
    (live : liveComponent pre.trace i = some k)
    (hf : (openHistory pre.trace k).head? = some first) :
    selected.env = first.selected.env := by
  exact host.componentSelectionEnvironments .incr prog start pre operational
    selection selected chosen p i k first noinit head live (first_open_mem hf)

/-- At selection of an existing progressed slot, its historical fold applies
in the selected environment. Sandbox preservation is kept explicit here. -/
theorem selected_progressed_fold (commands : WellFormedCommands m)
    {pre : Prefix m h .incr prog start} (host : HostWellFormed m h)
    (operational : Operational pre) (prefixes : CacheablePrefixes pre.trace pre.final)
    {selection : Selection sig} {selected : World sig}
    (chosen : h.select prog pre.final selection selected)
    {p : sig.Probe} {i : Nat} {k : Component} {sb : Sandbox sig}
    {first : StepDerivation m h .incr prog}
    (noinit : selection.init = none) (head : selection.head = .pipeline p i)
    (hs : FMap.get pre.final.sandbox i = some sb)
    (live : liveComponent pre.trace i = some k)
    (hf : (openHistory pre.trace k).head? = some first)
    (firsthead : first.selection.head = .pipeline p i) (hc : Cacheable m p)
    {input : Chunk} {result : Result sig}
    (call : m.denotes p input sb.view selected.env result) :
    let flags := operational.openSandboxes host i sb hs
    m.denotes p (sb.input ++'(flags.1) input) sb.base selected.env
      (combineResults (sandboxResult sb) result flags.2) := by
  have he := selected_historical_env host operational chosen noinit head live hf
  rw [he] at call ⊢
  exact progressed_next_call_folds commands host operational prefixes
    i sb k first p hs live hf firsthead hc input result call

/-- `def:paper-cache-wf` is preserved by insertion of a complete denotation
certificate. -/
theorem cache_insert {cache : Cache sig} (wf : WellFormedCache m cache)
    {p : sig.Probe} {env : Env sig} {input : Chunk} {fs : FS sig} {memo : Memo sig}
    (hc : Cacheable m p) (he : input.flag = .eof)
    (denoted : m.denotes p input fs env memo.result) :
    WellFormedCache m (FMap.set cache (cacheKey m p env input) memo) := by
  classical
  intro key value hv
  by_cases hk : key = cacheKey m p env input
  · subst key
    rw [FMap.get_set_self] at hv
    cases Option.some.inj hv
    exact ⟨p, env, input, fs, hc, he, rfl, denoted⟩
  · rw [FMap.get_set_other hk] at hv
    exact wf key value hv

/-- A closing folded result is exactly the memo installed by the raw rule. -/
theorem accumulated_memo_result (sb : Sandbox sig) (input : Chunk)
    (result : Result sig) (es : Nat) (hi : sb.input.flag = .open)
    (ho : sb.output.flag = .open) (he : result.output.flag = .eof)
    (hs : result.status = some es) :
    (accumulatedMemo sb input result es hi ho he).result =
      combineResults (sandboxResult sb) result ho := by
  cases result
  simp only at hs
  subst_vars
  rfl

/-- An open folded result is exactly the updated accumulated-prefix result. -/
theorem accumulated_open_result (sb : Sandbox sig) (input : Chunk)
    (result : Result sig) (hi : sb.input.flag = .open)
    (ho : sb.output.flag = .open) (hs : result.status = none) :
    sandboxResult (sb.accumulate input result hi ho) =
      combineResults (sandboxResult sb) result ho := by
  cases result
  simp only at hs
  subst_vars
  rfl

/-- The first open call establishes a prefix equation without an empty-input call. -/
theorem first_open_denotation {p : sig.Probe} {fs : FS sig} {env : Env sig}
    {input : Chunk} {result : Result sig} (hs : result.status = none)
    (call : m.denotes p input (Sandbox.initial fs).view env result) :
    m.denotes p ((Sandbox.initial fs).accumulate input result rfl rfl).input fs env
      (sandboxResult ((Sandbox.initial fs).accumulate input result rfl rfl)) := by
  convert fold_initial call using 1
  · rfl
  · exact accumulated_open_result _ _ _ _ _ hs

/-- A progressed open call updates the accumulated-prefix denotation. -/
theorem progressed_open_denotation (commands : WellFormedCommands m)
    {p : sig.Probe} (hc : Cacheable m p) {sb : Sandbox sig} {env : Env sig}
    (hi : sb.input.flag = .open) (ho : sb.output.flag = .open)
    (denoted : m.denotes p sb.input sb.base env (sandboxResult sb))
    {input : Chunk} {result : Result sig} (hs : result.status = none)
    (call : m.denotes p input sb.view env result) :
    m.denotes p (sb.accumulate input result hi ho).input sb.base env
      (sandboxResult (sb.accumulate input result hi ho)) := by
  rw [accumulated_open_result _ _ _ _ _ hs]
  exact fold_progressed commands hc hi ho denoted call

/-- Raw cache preservation needs only the selected sandbox's fold equation.
The equation uses the selected environment; H2/O1 must supply its historical equality. -/
theorem incr_cache_preservation {w w' : World sig} {head : Head sig} {out : Option Chunk}
    (wf : WellFormedCache m w.cache)
    (folds : ∀ (p : sig.Probe) (i : Nat) (sb : Sandbox sig),
      head = .pipeline p i → FMap.get w.sandbox i = some sb → Cacheable m p →
      ∀ (input : Chunk) (result : Result sig)
        (hi : sb.input.flag = .open) (ho : sb.output.flag = .open),
        m.denotes p input sb.view w.env result →
        m.denotes p (Chunk.concat sb.input input hi) sb.base w.env
          (combineResults (sandboxResult sb) result ho))
    (d : IncrDerivation m w head w' out) : WellFormedCache m w'.cache := by
  cases d with
  | pipelineOpen => exact wf
  | uncacheClose => exact wf
  | cacheCloseHit => exact wf
  | uncacheStandalone => exact wf
  | cacheStandaloneHit => exact wf
  | cacheCloseMiss p i sb s r es buffers out hc hb hs hi ho hm call hstatus hf hp =>
    apply cache_insert (fs := sb.base) wf hc rfl
    change m.denotes p (sb.input ++'hi ⟨s, .eof⟩) sb.base w.env
      (accumulatedMemo sb ⟨s, .eof⟩ r es hi ho hf).result
    rw [accumulated_memo_result sb _ r es hi ho hf hstatus]
    exact folds p i sb rfl hs hc _ r hi ho call
  | cacheStandaloneMiss p s r es hc hin hm call hstatus hf =>
    apply cache_insert wf hc rfl
    convert call using 1
    cases r
    simp only at hstatus
    subst_vars
    rfl

end

end Incr.Incr.CachePrefixes


