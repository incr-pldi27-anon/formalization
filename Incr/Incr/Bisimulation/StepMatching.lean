import Incr.Incr.Bisimulation.PrefixProperties
import Incr.Incr.Bisimulation.Observations
import Incr.Incr.Preservation.Components
import Incr.Incr.Bisimulation.RunLifting
import Incr.Incr.Math.PatchAlgebra
import Incr.Incr.Reuse.Proof

/-! # Strong bisimulation (`thm:paper-bisimulation`): host transport, raw rule
matching, views, and fresh records

These helpers do not yet construct either full admissible `PrefixStep`
implication. Their collector and post-step relation premises remain explicit.
-/

open Incr
namespace Incr.Incr.C8Steps

noncomputable section

variable {sig : Signature} {m : CommandModel sig} {h : Host sig}
  {prog : sig.Prog} {start : World sig}

/-- Matched final control follows from connected paired records, including zero steps. -/
theorem final_control {left : Trace m h .incr prog} {right : Trace m h .vanilla prog}
    (paired : List.Forall₂ PaperStepsMatch left right)
    {li rv lf rf : World sig} (lc : Connected li left lf) (rc : Connected rv right rf)
    (initial : ControlAgree li rv) : ControlAgree lf rf := by
  induction paired generalizing li rv with
  | nil => cases lc; cases rc; exact initial
  | cons matched rest ih =>
    cases lc
    cases rc
    exact ih (by assumption) (by assumption) matched.2.2.1

/-- `def:paper-bisim-relation` retains enough control information to invoke H4 at
the current boundary. -/
theorem related_control {witnesses : WitnessMap sig}
    {incr : Prefix m h .incr prog start} {vanilla : Prefix m h .vanilla prog start}
    (related : BisimRelated witnesses incr vanilla) : ControlAgree incr.final vanilla.final :=
  final_control related.steps incr.connected vanilla.connected ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The recorded initialization schedule determines absolute live component identities. -/
theorem live_components {left : Trace m h .incr prog} {right : Trace m h .vanilla prog}
    (paired : List.Forall₂ PaperStepsMatch left right) (i : Nat) :
    liveComponent left i = liveComponent right i := by
  have hm : left.map (fun d => d.selection.init.map (·.probes)) =
      right.map (fun d => d.selection.init.map (·.probes)) := by
    induction paired with
    | nil => rfl
    | cons matched rest ih => simp only [List.map_cons, matched.2.2.2.2, ih]
  have hidx : left.mapIdx (fun pos d => d.selection.init.map fun _ => pos) =
      right.mapIdx (fun pos d => d.selection.init.map fun _ => pos) := by
    have he := congrArg (fun xs => xs.mapIdx fun pos init => init.map fun _ => pos) hm
    have map_comp {α β γ : Type} (xs : List α) (f : α → β) (g : Nat → β → γ) :
        (xs.map f).mapIdx g = xs.mapIdx (fun n a => g n (f a)) := by
      apply List.ext_getElem <;> simp
    rw [map_comp left, map_comp right] at he
    simpa only [Option.map_map, Function.comp_def] using he
  have erase {executor : Executor} (xs : Trace m h executor prog) :
      (latestPipeline xs).map Prod.fst =
        ((xs.mapIdx fun pos d => d.selection.init.map fun _ => pos).filterMap id).getLast? := by
    unfold latestPipeline
    rw [← List.getLast?_map, List.map_filterMap]
    simp only [List.mapIdx_eq_zipIdx_map, List.filterMap_map,
      Function.comp_def, id_eq, Option.map_map]
  unfold liveComponent
  have hi := congrArg (fun xs => (xs.filterMap id).getLast?) hidx
  rw [← erase left, ← erase right] at hi
  simpa only [Option.map_map, Function.comp_def] using
    congrArg (Option.map fun pos => Component.pipeline pos i) hi

/-- H4 applies in both directions to arbitrary related admissible prefixes. -/
theorem selections_transport (host : HostWellFormed m h) {witnesses : WitnessMap sig}
    {incr : Prefix m h .incr prog start} {vanilla : Prefix m h .vanilla prog start}
    (related : BisimRelated witnesses incr vanilla) :
    SelectionsTransport h prog incr.final vanilla.final ∧
      SelectionsTransport h prog vanilla.final incr.final := by
  apply host.selectionWithPending prog start start incr vanilla
    related.incrAdmissible.operational related.vanillaAdmissible.operational
  · intro i _
    exact live_components related.steps i
  · exact related.sandboxDomains
  · exact related_control related
  · exact related.disjointPatches
  · exact related.overlay

/-- H1 and H4 together give selected control, including the selected status. -/
theorem forward_selection (host : HostWellFormed m h) {witnesses : WitnessMap sig}
    {incr : Prefix m h .incr prog start} {vanilla : Prefix m h .vanilla prog start}
    (related : BisimRelated witnesses incr vanilla) (selection : Selection sig)
    (selected : World sig) (chosen : h.select prog incr.final selection selected) :
    ∃ selection' selected', h.select prog vanilla.final selection' selected' ∧
      MatchingSelections selection selection' selected selected' ∧
      ControlAgree selected selected' := by
  obtain ⟨selection', selected', chosen', matched⟩ :=
    (selections_transport host related).1 selection selected chosen
  have li := host.selectionDiscipline _ _ _ incr related.incrAdmissible.operational
    selection selected chosen
  have rv := host.selectionDiscipline _ _ _ vanilla related.vanillaAdmissible.operational
    selection' selected' chosen'
  exact ⟨selection', selected', chosen', matched, matched.2.2.1,
    li.2.1.trans ((related_control related).2.1.trans rv.2.1.symm),
    matched.2.2.2.1, matched.2.2.2.2.1, matched.2.2.2.2.2⟩

/-- The reverse H4 selection requires no future completion or program isolation axiom. -/
theorem backward_selection (host : HostWellFormed m h) {witnesses : WitnessMap sig}
    {incr : Prefix m h .incr prog start} {vanilla : Prefix m h .vanilla prog start}
    (related : BisimRelated witnesses incr vanilla) (selection : Selection sig)
    (selected : World sig) (chosen : h.select prog vanilla.final selection selected) :
    ∃ selection' selected', h.select prog incr.final selection' selected' ∧
      MatchingSelections selection selection' selected selected' ∧
      ControlAgree selected selected' := by
  obtain ⟨selection', selected', chosen', matched⟩ :=
    (selections_transport host related).2 selection selected chosen
  have li := host.selectionDiscipline _ _ _ vanilla related.vanillaAdmissible.operational
    selection selected chosen
  have rv := host.selectionDiscipline _ _ _ incr related.incrAdmissible.operational
    selection' selected' chosen'
  exact ⟨selection', selected', chosen', matched, matched.2.2.1,
    li.2.1.trans ((related_control related).2.1.symm.trans rv.2.1.symm),
    matched.2.2.2.1, matched.2.2.2.2.1, matched.2.2.2.2.2⟩

/-- Dependency transport followed by retimestamping avoids every supplied record. -/
theorem transport_fresh (commands : WellFormedCommands m)
    {p : sig.Probe} {input : Chunk} {fs target live : FS sig} {env : Env sig}
    {r : Result sig} (call : m.denotes p input fs env r)
    (agreement : FSApprox (fs ↾ (FMap.dom r.reads ∪ FMap.dom r.writes))
      (target ↾ (FMap.dom r.reads ∪ FMap.dom r.writes))) (records : Records sig) :
    ∃ r', m.denotes p input target env r' ∧ r'.status = r.status ∧
      r'.output = r.output ∧ r'.writes = r.writes ∧
      FMap.dom r'.reads = FMap.dom r.reads ∧ PatchApprox r'.patch r.patch ∧
      FreshPatch r'.patch target live ∧
      (∀ q f, FMap.get r'.patch q = some (.write f) →
        ∀ q' old, (q', old) ∈ records → f.mtime ≠ old.mtime) := by
  classical
  obtain ⟨patch, reads, call', approx, domains, _⟩ :=
    commands.dependencies.transport p input fs env r call target agreement
  let all := records ++ (fsRecords target ++ fsRecords live)
  let used : Set sig.MTime := {t | t ∈ all.map (fun x => x.2.mtime)}
  have finite : used.Finite := List.finite_toSet _
  obtain ⟨patch', approx', fresh⟩ := commands.timestamps.fresh used finite patch
  have retimed := commands.timestamps.retimestamp p input target env
    {r with patch := patch, reads := reads} call' patch' approx'
  refine ⟨{r with patch := patch', reads := reads}, retimed, rfl, rfl, rfl,
    domains, ⟨approx'.1.trans approx.1, fun q hq =>
      (approx'.2 q hq).trans (approx.2 q (approx'.1 ▸ hq))⟩, ?_, ?_⟩
  · intro q f hf q' old hold same
    apply fresh q f hf
    change f.mtime ∈ all.map (fun x => x.2.mtime)
    rw [same]
    apply List.mem_map.mpr
    refine ⟨(q', old), ?_, rfl⟩
    rcases hold with ht | hl
    · exact List.mem_append.mpr (Or.inr (List.mem_append_left _ (mem_fsRecords_of_get ht)))
    · exact List.mem_append.mpr (Or.inr (List.mem_append_right _ (mem_fsRecords_of_get hl)))
  · intro q f hf q' old hold same
    apply fresh q f hf
    change f.mtime ∈ all.map (fun x => x.2.mtime)
    rw [same]
    exact List.mem_map.mpr ⟨(q', old), List.mem_append_left _ hold, rfl⟩

/-- Equal cumulative paths transport isolation without a terminating continuation. -/
theorem isolation_transport {left : Trace m h .incr prog}
    {right : Trace m h .vanilla prog} (paths : PathSetsAgree left right) :
    Isolated left ↔ Isolated right := by
  constructor <;> intro isolated entry i j distinct
  · rw [← (paths (.pipeline entry i)).1, ← (paths (.pipeline entry j)).2]
    exact isolated entry i j distinct
  · rw [(paths (.pipeline entry i)).1, (paths (.pipeline entry j)).2]
    exact isolated entry i j distinct

/-- Once a call has been transported, all seven Incr rule cases route identically
through the corresponding vanilla constructor. Hit calls are reconstructed witnesses. -/
theorem forward_probe {w v after : World sig} {head : Head sig} {out : Option Chunk}
    (d : IncrDerivation m w head after out) (control : ControlAgree w v)
    (r : Result sig)
    (call : m.denotes (match head with | .pipeline p _ => p | .standalone p => p)
      (IncrDerivation.input d) v.fs v.env r)
    (status : r.status = (IncrDerivation.result d).status)
    (output : r.output = IncrDerivation.produced d) :
    ∃ vafter, ∃ vd : VanillaDerivation m v head vafter out,
      ControlAgree after vafter ∧ VanillaDerivation.input vd = IncrDerivation.input d ∧
      VanillaDerivation.result vd = r := by
  obtain ⟨pc, oldStatus, env, buffersEq, stdinEq⟩ := control
  cases d with
  | pipelineOpen p i sb taken remaining original buffers out hb hs hi ho hc hstatus hflag hp =>
    dsimp only [IncrDerivation.input, IncrDerivation.result, IncrDerivation.produced] at call status output ⊢
    refine ⟨_, .openStep v p i taken remaining r buffers out
      (by simpa only [← buffersEq] using hb) call (status.trans hstatus)
      (by simpa only [output] using hflag)
      (by simpa only [updateBuffer, ← buffersEq, output] using hp), ?_⟩
    exact ⟨⟨pc, oldStatus, env, rfl, stdinEq⟩, rfl, rfl⟩
  | uncacheClose p i sb s original es buffers out hn hb hs hc hstatus hflag hp =>
    dsimp only [IncrDerivation.input, IncrDerivation.result, IncrDerivation.produced] at call status output ⊢
    refine ⟨_, .closeStep v p i s r es buffers out
      (by simpa only [← buffersEq] using hb) call (status.trans hstatus)
      (by simpa only [output] using hflag) (by simpa only [← buffersEq, output] using hp), ?_⟩
    exact ⟨⟨pc, rfl, env, rfl, stdinEq⟩, rfl, rfl⟩
  | cacheCloseMiss p i sb s original es buffers out cacheable hb hs hi ho miss hc hstatus hflag hp =>
    dsimp only [IncrDerivation.input, IncrDerivation.result, IncrDerivation.produced] at call status output ⊢
    refine ⟨_, .closeStep v p i s r es buffers out
      (by simpa only [← buffersEq] using hb) call (status.trans hstatus)
      (by simpa only [output] using hflag) (by simpa only [closeBuffer, ← buffersEq, output] using hp), ?_⟩
    exact ⟨⟨pc, rfl, env, rfl, stdinEq⟩, rfl, rfl⟩
  | cacheCloseHit p i sb s tail memo buffers out cacheable hb hs hi ho hm valid guard hp =>
    dsimp only [IncrDerivation.input, IncrDerivation.result, IncrDerivation.produced,
      Memo.result] at call status output ⊢
    refine ⟨_, .closeStep v p i s r memo.ec buffers out
      (by simpa only [← buffersEq] using hb) call status
      (by simp only [output]) (by simpa only [closeBuffer, ← buffersEq, output] using hp), ?_⟩
    exact ⟨⟨pc, rfl, env, rfl, stdinEq⟩, rfl, rfl⟩
  | uncacheStandalone p s original es cacheable hb hc hstatus =>
    dsimp only [IncrDerivation.input, IncrDerivation.result, IncrDerivation.produced] at call status output ⊢
    refine ⟨standaloneWorld v es r.patch, ?_, ?_⟩
    · rw [← output]
      exact .standalone v p s r es (by simpa only [← stdinEq] using hb)
        call (status.trans hstatus)
    · refine ⟨⟨pc, rfl, env, buffersEq, rfl⟩, ?_⟩
      cases r; cases original; dsimp at output; cases output; exact ⟨rfl, rfl⟩
  | cacheStandaloneMiss p s original es cacheable hb miss hc hstatus hflag =>
    dsimp only [IncrDerivation.input, IncrDerivation.result, IncrDerivation.produced] at call status output ⊢
    refine ⟨standaloneWorld v es r.patch, ?_, ?_⟩
    · rw [← output]
      exact .standalone v p s r es (by simpa only [← stdinEq] using hb)
        call (status.trans hstatus)
    · refine ⟨⟨pc, rfl, env, buffersEq, rfl⟩, ?_⟩
      cases r; cases original; dsimp at output; cases output; exact ⟨rfl, rfl⟩
  | cacheStandaloneHit p s memo cacheable hb hm valid flag =>
    dsimp only [IncrDerivation.input, IncrDerivation.result, IncrDerivation.produced,
      Memo.result] at call status output ⊢
    refine ⟨standaloneWorld v memo.ec r.patch, ?_, ?_⟩
    · rw [← output]
      exact .standalone v p s r memo.ec (by simpa only [← stdinEq] using hb) call status
    · refine ⟨⟨pc, rfl, env, buffersEq, rfl⟩, ?_⟩
      cases r; cases memo; dsimp at output; cases output; exact ⟨rfl, rfl⟩

/-- A transported open call supplies the Incr open rule and identical routing. -/
theorem backward_open {w v : World sig} (control : ControlAgree w v)
    (p : sig.Probe) (i : Nat) (sb : Sandbox sig) (taken remaining : Bytes)
    (r : Result sig) (buffers : FMap Nat Chunk) (out : Option Chunk)
    (sandbox : FMap.get w.sandbox i = some sb)
    (inputOpen : sb.input.flag = .open) (outputOpen : sb.output.flag = .open)
    (buffer : FMap.get v.buffer i = some ⟨taken ++ remaining, .open⟩)
    (call : m.denotes p ⟨taken, .open⟩ sb.view w.env r)
    (status : r.status = none) (flag : r.output.flag = .open)
    (route : put (v.buffer[i ↦ ⟨remaining, .open⟩]) i r.output = some (buffers, out)) :
    ∃ after, ∃ d : IncrDerivation m w (.pipeline p i) after out,
      ControlAgree after {v with fs := applyPatch v.fs r.patch, buffer := buffers} ∧
      IncrDerivation.input d = ⟨taken, .open⟩ ∧ IncrDerivation.result d = r := by
  obtain ⟨pc, oldStatus, env, buffersEq, stdinEq⟩ := control
  refine ⟨_, .pipelineOpen w p i sb taken remaining r buffers out
    (by simpa only [buffersEq] using buffer) sandbox inputOpen outputOpen call status flag
    (by simpa only [updateBuffer, buffersEq] using route), ?_⟩
  exact ⟨⟨pc, oldStatus, env, rfl, stdinEq⟩, rfl, rfl⟩

/-- A transported non-cacheable closing call supplies the Incr close constructor. -/
theorem backward_uncache_close {w v : World sig} (control : ControlAgree w v)
    (p : sig.Probe) (i : Nat) (sb : Sandbox sig) (s : Bytes)
    (r : Result sig) (es : Nat) (buffers : FMap Nat Chunk) (out : Option Chunk)
    (noncacheable : ¬ Cacheable m p) (sandbox : FMap.get w.sandbox i = some sb)
    (buffer : FMap.get v.buffer i = some ⟨s, .eof⟩)
    (call : m.denotes p ⟨s, .eof⟩ sb.view w.env r)
    (status : r.status = some es) (flag : r.output.flag = .eof)
    (route : put (v.buffer ∖ i) i r.output = some (buffers, out)) :
    ∃ after, ∃ d : IncrDerivation m w (.pipeline p i) after out,
      ControlAgree after (closeWorld v i es r.patch buffers) ∧
      IncrDerivation.input d = ⟨s, .eof⟩ ∧ IncrDerivation.result d = r := by
  obtain ⟨pc, oldStatus, env, buffersEq, stdinEq⟩ := control
  refine ⟨_, .uncacheClose w p i sb s r es buffers out noncacheable
    (by simpa only [buffersEq] using buffer) sandbox call status flag
    (by simpa only [buffersEq] using route), ?_⟩
  exact ⟨⟨pc, rfl, env, rfl, stdinEq⟩, rfl, rfl⟩

/-- A transported non-cacheable standalone call consumes the same stdin. -/
theorem backward_uncache_standalone {w v : World sig} (control : ControlAgree w v)
    (p : sig.Probe) (s : Bytes) (r : Result sig) (es : Nat)
    (noncacheable : ¬ Cacheable m p) (stdin : v.stdin = ⟨s, .eof⟩)
    (call : m.denotes p ⟨s, .eof⟩ w.fs w.env r) (status : r.status = some es) :
    ∃ after, ∃ d : IncrDerivation m w (.standalone p) after (some r.output),
      ControlAgree after (standaloneWorld v es r.patch) ∧
      IncrDerivation.input d = ⟨s, .eof⟩ ∧ IncrDerivation.result d = r := by
  obtain ⟨pc, oldStatus, env, buffersEq, stdinEq⟩ := control
  refine ⟨_, .uncacheStandalone w p s r es noncacheable (stdinEq.trans stdin) call status, ?_⟩
  exact ⟨⟨pc, rfl, env, buffersEq, rfl⟩, rfl, rfl⟩

/-- Source-edge isolation excludes every older other-component write, not only
writes of still-live slots. The full successor access set is retained. -/
theorem incr_edge_exclusion {witnesses : WitnessMap sig}
    {incr incr' : Prefix m h .incr prog start} {vanilla : Prefix m h .vanilla prog start}
    {label : Head sig} (related : BisimRelated witnesses incr vanilla)
    (edge : PrefixStep witnesses label incr incr') (entry i j : Nat) (different : i ≠ j) :
    Disjoint (componentAccesses incr'.trace (.pipeline entry i))
      (componentWrites vanilla.trace (.pipeline entry j)) := by
  obtain ⟨_, admitted, d, trace, _, _, _⟩ := edge
  rw [← (related.paths (.pipeline entry j)).1]
  apply Set.disjoint_left.mpr
  intro q access written
  apply Set.disjoint_left.mp (admitted.isolated entry j i different.symm)
  · obtain ⟨old, member, path⟩ := written
    exact ⟨old, trace ▸ C9.componentSteps_append_subset incr.trace [d] _ old member, path⟩
  · exact access

/-- The reverse exclusion uses the vanilla successor's given isolation. -/
theorem vanilla_edge_exclusion {witnesses : WitnessMap sig}
    {incr : Prefix m h .incr prog start} {vanilla vanilla' : Prefix m h .vanilla prog start}
    {label : Head sig} (related : BisimRelated witnesses incr vanilla)
    (edge : PrefixStep witnesses label vanilla vanilla') (entry i j : Nat) (different : i ≠ j) :
    Disjoint (componentAccesses vanilla'.trace (.pipeline entry i))
      (componentWrites incr.trace (.pipeline entry j)) := by
  obtain ⟨_, admitted, d, trace, _, _, _⟩ := edge
  rw [(related.paths (.pipeline entry j)).1]
  apply Set.disjoint_left.mpr
  intro q access written
  apply Set.disjoint_left.mp (admitted.isolated entry j i different.symm)
  · obtain ⟨old, member, path⟩ := written
    exact ⟨old, trace ▸ C9.componentSteps_append_subset vanilla.trace [d] _ old member, path⟩
  · exact access

/-- Standalone backward dispatch chooses non-cacheable, miss, or valid-hit rules.
The witness premise is the selected-world instance of `lem:paper-bisim-prefix`
cache provenance. -/
theorem backward_standalone (shape : DenotationShape m) (commands : WellFormedCommands m)
    (key : HashInjective m) {w v : World sig} (control : ControlAgree w v)
    (cache : WellFormedCache m w.cache)
    (witnesses : ∀ k memo, FMap.get w.cache k = some memo →
      ∃ fs, EntryWitness m k memo fs ∧ TimestampConsistent ({recordOfFS fs} ∪ {recordOfFS w.fs}))
    (p : sig.Probe) (s : Bytes) (r : Result sig) (es : Nat)
    (stdin : v.stdin = ⟨s, .eof⟩)
    (call : m.denotes p ⟨s, .eof⟩ w.fs w.env r) (status : r.status = some es) :
    ∃ after out, ∃ d : IncrDerivation m w (.standalone p) after out,
      ControlAgree after (standaloneWorld v es r.patch) ∧ out = some r.output ∧
      IncrDerivation.produced d = r.output ∧
      PatchApprox (IncrDerivation.result d).patch r.patch ∧
      FMap.dom (IncrDerivation.result d).reads = FMap.dom r.reads ∧
      (IncrDerivation.result d).writes = r.writes := by
  classical
  obtain ⟨pc, oldStatus, env, buffersEq, stdinEq⟩ := control
  have stdin' := stdinEq.trans stdin
  have flag := (shape _ _ _ _ _ call).2 rfl |>.1
  have reflexive : PatchApprox r.patch r.patch := ⟨rfl, fun _ _ => rfl⟩
  by_cases cacheable : Cacheable m p
  · cases found : FMap.get w.cache (cacheKey m p w.env ⟨s, .eof⟩) with
    | none =>
      refine ⟨_, _, .cacheStandaloneMiss w p s r es cacheable stdin'
        (Or.inl found) call status flag, ?_⟩
      exact ⟨⟨pc, rfl, env, buffersEq, rfl⟩, rfl, rfl, reflexive, rfl, rfl⟩
    | some memo =>
      by_cases valid : Valid m memo.reads memo.writes w.fs
      · obtain ⟨fs, witness, timestamps⟩ := witnesses _ memo found
        have reused := validation_and_cache_reuse shape commands key w.cache cache
          p w.env ⟨s, .eof⟩ memo fs w.fs rfl found witness valid timestamps
        have comparison := reused.2.2 r call
        have fields := comparison.1
        simp only [Prod.mk.injEq, Memo.result] at fields
        have sameStatus : memo.ec = es :=
          Option.some.inj (fields.1.symm.trans status)
        have patch : PatchApprox memo.patch r.patch :=
          ⟨comparison.2.1.symm, fun q hq =>
            (comparison.2.2 q (comparison.2.1.symm ▸ hq)).symm⟩
        refine ⟨_, _, .cacheStandaloneHit w p s memo cacheable stdin' found valid memo.output_eof, ?_⟩
        exact ⟨⟨pc, sameStatus, env, buffersEq, rfl⟩,
          congrArg some fields.2.2.2.symm, fields.2.2.2.symm, patch,
          congrArg FMap.dom fields.2.1.symm, fields.2.2.1.symm⟩
      · refine ⟨_, _, .cacheStandaloneMiss w p s r es cacheable stdin'
          (Or.inr ⟨memo, found, valid⟩) call status flag, ?_⟩
        exact ⟨⟨pc, rfl, env, buffersEq, rfl⟩, rfl, rfl, reflexive, rfl, rfl⟩
  · refine ⟨_, _, .uncacheStandalone w p s r es cacheable stdin' call status, ?_⟩
    exact ⟨⟨pc, rfl, env, buffersEq, rfl⟩, rfl, rfl, reflexive, rfl, rfl⟩

/-- The final world's actual records are retained even at length zero. -/
theorem final_world_records {executor : Executor}
    (pre : Prefix m h executor prog start) (record : sig.Path × File sig)
    (member : record ∈ worldRecords pre.final) : record ∈ pre.records := by
  have collect {a b : World sig} {trace : Trace m h executor prog}
      (connected : Connected a trace b) (hr : record ∈ worldRecords b) :
      record ∈ worldRecords a ++ trace.flatMap StepDerivation.records := by
    induction connected with
    | nil => exact List.mem_append_left _ hr
    | cons d rest final tail ih =>
      rcases List.mem_append.mp (ih hr) with after | later
      · apply List.mem_append_right
        apply List.mem_flatMap.mpr
        refine ⟨d, by simp, ?_⟩
        simp only [StepDerivation.records, List.mem_append]
        tauto
      · exact List.mem_append_right _ (by simpa only [List.flatMap_cons, List.mem_append] using Or.inr later)
  exact collect pre.connected member

/-- The final world's whole maps belong to the actual prefix inventory. -/
theorem final_world_paper_records {executor : Executor}
    (pre : Prefix m h executor prog start) {record : RecordMap sig}
    (member : record ∈ worldPaperRecords pre.final) : record ∈ pre.paperRecords := by
  have collect {a b : World sig} {trace : Trace m h executor prog}
      (connected : Connected a trace b) (hr : record ∈ worldPaperRecords b) :
      record ∈ worldPaperRecords a ∪ {r | ∃ d ∈ trace, r ∈ d.paperRecords} := by
    induction connected with
    | nil => exact Or.inl hr
    | cons d rest final tail ih =>
      rcases ih hr with after | ⟨later, laterAt, laterRecord⟩
      · exact Or.inr ⟨d, by simp, Or.inl (Or.inl (Or.inl (Or.inr after)))⟩
      · exact Or.inr ⟨later, List.mem_cons_of_mem _ laterAt, laterRecord⟩
  exact collect pre.connected member

/-- `lem:paper-bisim-prefix` witnesses remain valid provenance certificates after
host selection.
Whole-map witness provenance is not replaced by flattened-record membership. -/
theorem selected_cache_witnesses (host : HostWellFormed m h)
    {witnesses : WitnessMap sig} (pre : Prefix m h .incr prog start)
    (admitted : Admissible witnesses pre) (properties : BisimPrefixProperties witnesses pre)
    {selection : Selection sig} {selected : World sig}
    (chosen : h.select prog pre.final selection selected) :
    ∀ k memo, FMap.get selected.cache k = some memo →
      ∃ fs, EntryWitness m k memo fs ∧ TimestampConsistent ({recordOfFS fs} ∪ {recordOfFS selected.fs}) := by
  intro k memo found
  have discipline := host.selectionDiscipline _ _ _ pre admitted.operational _ _ chosen
  rw [discipline.2.2.1] at found
  obtain ⟨p, env, witness, cacheable, eof, key, call, _, consistent⟩ := properties.1 k memo found
  refine ⟨witness.fs, ⟨p, env, witness.input, cacheable, eof, key, call⟩, ?_⟩
  apply consistent.mono
  intro record hr
  rcases hr with old | live
  · exact Or.inr old
  · have equality : record = recordOfFS selected.fs := Set.mem_singleton_iff.mp live
    subst record
    apply Or.inl
    rw [discipline.1]
    exact final_world_paper_records pre (world_fs_mem_paperRecords pre.final)

/-- At a cacheable close, a live folded denotation decides the exact miss/hit
rule. A valid memo proves the output-prefix guard rather than assuming it. -/
theorem backward_cache_close (shape : DenotationShape m) (commands : WellFormedCommands m)
    (key : HashInjective m) {w v : World sig} (control : ControlAgree w v)
    (cache : WellFormedCache m w.cache)
    (witnesses : ∀ k memo, FMap.get w.cache k = some memo →
      ∃ fs, EntryWitness m k memo fs ∧ TimestampConsistent ({recordOfFS fs} ∪ {recordOfFS w.fs}))
    (p : sig.Probe) (i : Nat) (sb : Sandbox sig) (s : Bytes)
    (r : Result sig) (es : Nat) (buffers : FMap Nat Chunk) (out : Option Chunk)
    (cacheable : Cacheable m p) (sandbox : FMap.get w.sandbox i = some sb)
    (hi : sb.input.flag = .open) (ho : sb.output.flag = .open)
    (buffer : FMap.get v.buffer i = some ⟨s, .eof⟩)
    (call : m.denotes p ⟨s, .eof⟩ sb.view w.env r)
    (status : r.status = some es) (flag : r.output.flag = .eof)
    (route : put (v.buffer ∖ i) i r.output = some (buffers, out))
    (whole : m.denotes p (sb.input++'hi⟨s, .eof⟩) w.fs w.env
      (combineResults (sandboxResult sb) r ho)) :
    ∃ after returned, ∃ d : IncrDerivation m w (.pipeline p i) after returned,
      ControlAgree after (closeWorld v i es r.patch buffers) ∧ returned = out ∧
      IncrDerivation.produced d = r.output ∧
      PatchApprox ((IncrDerivation.livePatch d).getD ∅) (sb.patch ⊎ r.patch) := by
  classical
  obtain ⟨pc, oldStatus, env, buffersEq, stdinEq⟩ := control
  have buffer' : FMap.get w.buffer i = some ⟨s, .eof⟩ := by
    simpa only [buffersEq] using buffer
  have route' : put (w.buffer ∖ i) i r.output = some (buffers, out) := by
    simpa only [buffersEq] using route
  have reflexive : PatchApprox (sb.patch ⊎ r.patch) (sb.patch ⊎ r.patch) :=
    ⟨rfl, fun _ _ => rfl⟩
  cases found : FMap.get w.cache (cacheKey m p w.env (sb.input ++'hi ⟨s, .eof⟩)) with
  | none =>
    refine ⟨_, _, .cacheCloseMiss w p i sb s r es buffers out cacheable buffer' sandbox hi ho
      ((cacheMiss_iff_not_useCache m w _).mp (Or.inl found)) call status flag route', ?_⟩
    exact ⟨⟨pc, rfl, env, rfl, stdinEq⟩, rfl, rfl, reflexive⟩
  | some memo =>
    by_cases valid : Valid m memo.reads memo.writes w.fs
    · obtain ⟨fs, witness, timestamps⟩ := witnesses _ memo found
      have reused := validation_and_cache_reuse shape commands key w.cache cache
        p w.env (sb.input ++'hi ⟨s, .eof⟩) memo fs w.fs rfl found witness valid timestamps
      have comparison := reused.2.2 _ whole
      have fields := comparison.1
      simp only [Prod.mk.injEq, combineResults, sandboxResult, Memo.result] at fields
      have sameStatus : memo.ec = es := Option.some.inj (fields.1.symm.trans status)
      have outputEq : r.output = ⟨r.output.bytes, .eof⟩ := by
        cases he : r.output with | mk bytes f => simp_all
      have guard : memo.output = sb.output ++'ho ⟨r.output.bytes, .eof⟩ := by
        rw [← outputEq]
        exact fields.2.2.2.symm
      have patch : PatchApprox memo.patch (sb.patch ⊎ r.patch) :=
        ⟨comparison.2.1.symm, fun q hq =>
          (comparison.2.2 q (comparison.2.1.symm ▸ hq)).symm⟩
      refine ⟨_, _, .cacheCloseHit w p i sb s r.output.bytes memo buffers out cacheable
        buffer' sandbox hi ho found ((useCache_iff_of_get found).mpr valid) guard (by rw [← outputEq]; exact route'), ?_⟩
      exact ⟨⟨pc, sameStatus, env, rfl, stdinEq⟩, rfl, outputEq.symm, patch⟩
    · refine ⟨_, _, .cacheCloseMiss w p i sb s r es buffers out cacheable buffer' sandbox hi ho
        ((cacheMiss_iff_not_useCache m w _).mp (Or.inr ⟨memo, found, valid⟩)) call status flag route', ?_⟩
      exact ⟨⟨pc, rfl, env, rfl, stdinEq⟩, rfl, rfl, reflexive⟩

/-- Other staged patches do not affect a queried path outside their domains. -/
theorem pending_lookup (w : World sig) (i : Nat) (sb : Sandbox sig)
    (present : FMap.get w.sandbox i = some sb) (q : sig.Path)
    (others : ∀ j other, j ≠ i → FMap.get w.sandbox j = some other →
      q ∉ FMap.dom other.patch) :
    FMap.get (pendingPatch w) q = FMap.get sb.patch q := by
  classical
  have slot : i ∈ w.sandbox.keys.sort (· ≤ ·) := by
    have hi : i ∈ FMap.dom w.sandbox :=
      Finmap.mem_keys.mpr (Finmap.mem_iff.mpr ⟨sb, present⟩)
    simpa only [Finset.mem_sort, FMap.dom, FMap.keys, Set.mem_ofPred_eq] using hi
  have absent j other (different : j ≠ i) (get : FMap.get w.sandbox j = some other) :
      FMap.get other.patch q = none :=
    FMap.get_eq_none.mpr (fun hm => others j other different get (Finmap.mem_keys.mpr hm))
  cases hp : FMap.get sb.patch q with
  | none =>
    have allAbsent j other (get : FMap.get w.sandbox j = some other) :
        FMap.get other.patch q = none := by
      by_cases same : j = i
      · subst j
        have he := Option.some.inj (present.symm.trans get)
        simpa only [← he] using hp
      · exact absent j other same get
    have fold (slots : List Nat) (acc : Patch sig) :
        FMap.get (slots.foldl (fun acc j => match FMap.get w.sandbox j with
          | none => acc | some other => acc ⊎ other.patch) acc) q = FMap.get acc q := by
      induction slots generalizing acc with
      | nil => rfl
      | cons j rest ih =>
        rw [List.foldl_cons]
        cases get : FMap.get w.sandbox j with
        | none => exact ih acc
        | some other =>
          rw [ih, FMap.get_merge_elim, allAbsent j other get]
          rfl
    exact fold _ ∅
  | some edit =>
    have fold (slots : List Nat) (acc : Patch sig)
        (initial : i ∈ slots ∨ FMap.get acc q = some edit) :
        FMap.get (slots.foldl (fun acc j => match FMap.get w.sandbox j with
          | none => acc | some other => acc ⊎ other.patch) acc) q = some edit := by
      induction slots generalizing acc with
      | nil => exact initial.resolve_left (by simp)
      | cons j rest ih =>
        rw [List.foldl_cons]
        by_cases same : j = i
        · subst j
          rw [present]
          exact ih _ (Or.inr (by simp [FMap.get_merge_elim, hp]))
        · cases get : FMap.get w.sandbox j with
          | none =>
            apply ih
            rcases initial with hin | he
            · exact Or.inl (List.mem_of_ne_of_mem (Ne.symm same) hin)
            · exact Or.inr he
          | some other =>
            apply ih
            rcases initial with hin | he
            · exact Or.inl (List.mem_of_ne_of_mem (Ne.symm same) hin)
            · right
              simpa [FMap.get_merge_elim, absent j other same get] using he
    exact fold _ ∅ (Or.inl slot)

/-- Patch lookup distinguishes writes, deletions, and unchanged paths. -/
theorem apply_lookup (fs : FS sig) (patch : Patch sig) (q : sig.Path) :
    FMap.get (applyPatch fs patch) q = match FMap.get patch q with
      | none => FMap.get fs q | some (.write file) => some file | some .delete => none := by
  classical
  cases get : FMap.get patch q with
  | none => exact Incr.applyPatch_get_none get
  | some edit => cases edit with
    | write file => exact Incr.applyPatch_get_write get
    | delete => exact Incr.applyPatch_get_delete get

/-- The `lem:paper-bisim-prefix` frame and exclusion of older other-component
writes identify the call filesystem with the pending overlay on the entire
enlarged access set. -/
theorem view_restrict_overlay {trace : Trace m h .incr prog} {w : World sig}
    {current : Option (Nat × PipelineInit sig)}
    (slices : LiveSliceProperties trace w current) (i : Nat) (sb : Sandbox sig)
    (present : FMap.get w.sandbox i = some sb) (entry : Nat) (init : PipelineInit sig)
    (entryEq : current = some (entry, init)) (Q : Set sig.Path)
    (excluded : Disjoint Q (otherWrites trace entry i)) :
    sb.view ↾ Q = (applyPatch w.fs (pendingPatch w)) ↾ Q := by
  classical
  obtain ⟨entry', init', currentEq, slice, _⟩ := slices i sb present
  have same := Option.some.inj (entryEq.symm.trans currentEq)
  cases same
  have base := slice.2.2 Q excluded
  apply FMap.restrict_congr
  intro q hq
  have baseGet : FMap.get sb.base q = FMap.get w.fs q := by
    have hget := congrArg (fun fs => FMap.get fs q) base
    simpa [FMap.get_restrict, hq] using hget
  have others : ∀ j other, j ≠ i → FMap.get w.sandbox j = some other →
      q ∉ FMap.dom other.patch := by
    intro j other different get written
    obtain ⟨otherEntry, otherInit, otherCurrent, otherSlice, _⟩ := slices j other get
    have same := Option.some.inj (entryEq.symm.trans otherCurrent)
    cases same
    apply Set.disjoint_left.mp excluded hq
    apply PrefixProperties.mem_otherWrites.mpr
    exact ⟨j, different, otherSlice.1.symm ▸ written⟩
  unfold Sandbox.view
  rw [apply_lookup, apply_lookup, pending_lookup w i sb present q others, baseGet]

/-- Empty accumulated patches have an empty pending overlay. -/
theorem pending_zero (w : World sig)
    (empty : ∀ i sb, FMap.get w.sandbox i = some sb → sb.patch = ∅) :
    pendingPatch w = ∅ := by
  classical
  have fold (slots : List Nat) (acc : Patch sig) :
      slots.foldl (fun acc i => match FMap.get w.sandbox i with
        | none => acc | some sb => acc ⊎ sb.patch) acc = acc := by
    induction slots generalizing acc with
    | nil => rfl
    | cons i rest ih =>
      rw [List.foldl_cons]
      cases get : FMap.get w.sandbox i with
      | none => exact ih acc
      | some sb => simpa [empty i sb get, FMap.merge] using ih (acc ⊎ sb.patch)
  exact fold _ ∅

/-- Host selection leaves the staged overlay unchanged, including new entries. -/
theorem selection_pending {executor : Executor} {trace : Trace m h executor prog}
    {before selected : World sig} {selection : Selection sig}
    (discipline : SelectionDiscipline trace before selection selected) :
    pendingPatch selected = pendingPatch before := by
  obtain ⟨_, _, _, init, _⟩ := discipline
  cases hinit : selection.init with
  | none =>
    simp only [hinit] at init
    simp only [pendingPatch, init.1]
  | some initialization =>
    simp only [hinit] at init
    have beforeZero : pendingPatch before = ∅ := pending_zero before (by simp [init.2.1, FMap.get])
    rw [beforeZero]
    apply pending_zero
    intro i sb get
    rw [init.2.2.2.2] at get
    have initial := initialSandboxes_get_eq initialization before.fs get
    simp only [initial, Sandbox.initial]

/-- Matched selections preserve the current overlay relation used by
`thm:paper-bisimulation`. -/
theorem selected_overlay (host : HostWellFormed m h) {witnesses : WitnessMap sig}
    {incr : Prefix m h .incr prog start} {vanilla : Prefix m h .vanilla prog start}
    (related : BisimRelated witnesses incr vanilla)
    {si sv : Selection sig} {wi wv : World sig}
    (hi : h.select prog incr.final si wi) (hv : h.select prog vanilla.final sv wv) :
    FSApprox wv.fs (applyPatch wi.fs (pendingPatch wi)) := by
  have di := host.selectionDiscipline _ _ _ incr related.incrAdmissible.operational _ _ hi
  have dv := host.selectionDiscipline _ _ _ vanilla related.vanillaAdmissible.operational _ _ hv
  rw [di.1, dv.1, selection_pending di]
  exact related.overlay

/-- The two call filesystems agree on every set excluded by source-edge isolation. -/
theorem call_agreement {trace : Trace m h .incr prog} {wi wv : World sig}
    {current : Option (Nat × PipelineInit sig)}
    (slices : LiveSliceProperties trace wi current)
    (overlay : FSApprox wv.fs (applyPatch wi.fs (pendingPatch wi)))
    (i : Nat) (sb : Sandbox sig) (present : FMap.get wi.sandbox i = some sb)
    (entry : Nat) (init : PipelineInit sig) (entryEq : current = some (entry, init))
    (Q : Set sig.Path) (excluded : Disjoint Q (otherWrites trace entry i)) :
    FSApprox (sb.view ↾ Q) (wv.fs ↾ Q) := by
  classical
  rw [view_restrict_overlay slices i sb present entry init entryEq Q excluded]
  apply FSApprox.of_contents
  intro q
  simp only [FMap.get_restrict]
  split
  · exact (overlay.contents q).symm
  · rfl

/-- A flattened patch record still identifies its unique map entry. -/
theorem patch_record_get {patch : Patch sig} {q : sig.Path} {file : File sig}
    (member : (q, file) ∈ patchRecords patch) :
    FMap.get patch q = some (.write file) := by
  classical
  obtain ⟨⟨path, edit⟩, entry, equal⟩ := List.mem_filterMap.mp member
  cases edit with
  | delete => contradiction
  | write f =>
    simp only [Option.some.injEq, Prod.mk.injEq] at equal
    obtain ⟨rfl, rfl⟩ := equal
    exact Finmap.lookup_eq_some_iff.mpr (Multiset.mem_toList.mp entry)

/-- Fresh patch records preserve consistency of all older retained records. -/
theorem fresh_patch_consistent (records : Records sig) (patch : Patch sig)
    (consistent : TimestampCompatible records)
    (fresh : ∀ q file, FMap.get patch q = some (.write file) →
      ∀ q' old, (q', old) ∈ records → file.mtime ≠ old.mtime) :
    TimestampCompatible (records ++ patchRecords patch) := by
  intro q f g hf hg same
  rcases List.mem_append.mp hf with oldF | patchF <;>
    rcases List.mem_append.mp hg with oldG | patchG
  · exact consistent q f g oldF oldG same
  · exact False.elim (fresh q g (patch_record_get patchG) q f oldF same.symm)
  · exact False.elim (fresh q f (patch_record_get patchF) q g oldG same)
  · have equal := Option.some.inj ((patch_record_get patchF).symm.trans (patch_record_get patchG))
    cases equal
    rfl

/-- Collector-origin proofs suffice to check a constructed successor inventory.
This lemma does not assert the required collector-origin premise. -/
theorem fresh_record_inventory (old records : Records sig) (patch : Patch sig)
    (consistent : TimestampCompatible old)
    (fresh : ∀ q file, FMap.get patch q = some (.write file) →
      ∀ q' previous, (q', previous) ∈ old → file.mtime ≠ previous.mtime)
    (sources : ∀ record ∈ records, record ∈ old ++ patchRecords patch) :
    TimestampCompatible records :=
  (fresh_patch_consistent old patch consistent fresh).mono sources

end
end Incr.Incr.C8Steps


