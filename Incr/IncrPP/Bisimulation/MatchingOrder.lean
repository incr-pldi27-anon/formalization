import Incr.IncrPP.Preservation.FreshRecords

/-!
# Transfer of exit ordering between matched traces

The proof uses original positions and every-prefix path sets. No cross-run
record-consistency assumption or synthetic component identity is added.
-/

namespace Incr.IncrPP

noncomputable section

variable {sig : Signature} {m : CommandModel sig} {h : Host sig}
  {executor : Executor} {prog : sig.Prog}

/-- An indexed access belongs to its component's cumulative access set. -/
theorem accessPosition_to_access (trace : Trace m h executor prog) (k : Component)
    (q : sig.Path) (position : Nat) (member : position ∈ accessPositions trace k q) :
    q ∈ componentAccesses trace k := by
  obtain ⟨pos, d, atPos, component, path, _⟩ := (mem_accessPositions_iff trace k q position).mp member
  have step := (mem_componentSteps_iff trace k d).mpr ⟨pos, atPos, component⟩
  rcases path with (patch | read) | write
  · exact Or.inr ⟨d, step, patch⟩
  · exact Or.inl ⟨d, step, Or.inl read⟩
  · exact Or.inl ⟨d, step, Or.inr write⟩

/-- Taking the prefix through an access retains that actual indexed access. -/
theorem accessPosition_take (trace : Trace m h executor prog) (k : Component)
    (q : sig.Path) (position : Nat) (member : position ∈ accessPositions trace k q)
    (n : Nat) (bound : position ≤ n) : q ∈ componentAccesses (trace.take n) k := by
  obtain ⟨pos, d, atPos, component, path, equal⟩ := (mem_accessPositions_iff trace k q position).mp member
  have inside : pos < n := by rw [equal] at bound; exact Nat.lt_of_succ_le bound
  have atShort : (trace.take n)[pos]? = some d := by
    simp only [List.getElem?_take, inside, ite_true]
    exact atPos
  have shortLength : pos < (trace.take n).length := (List.getElem?_eq_some_iff.mp atShort).choose
  have shortComponent : componentAt (trace.take n) pos d = some k := by
    have same := componentAt_append (trace.take n) (trace.drop n) pos d shortLength
    simpa only [List.take_append_drop, component] using same.symm
  have shortPosition : paperPosition pos ∈ accessPositions (trace.take n) k q :=
    (mem_accessPositions_iff (trace.take n) k q _).mpr ⟨pos, d, atShort, shortComponent, path, rfl⟩
  exact accessPosition_to_access _ _ _ _ shortPosition

/-- Each access in a taken prefix occurs no later than its endpoint. -/
theorem access_take_implies_first_le (trace : Trace m h executor prog) (k : Component)
    (q : sig.Path) (accessed : q ∈ componentAccesses trace k) (n : Nat)
    (shortAccess : q ∈ componentAccesses (trace.take n) k) : firstAccess trace k q accessed ≤ n := by
  obtain ⟨position, member⟩ := accessPosition_exists (trace.take n) k q shortAccess
  have longMember : position ∈ accessPositions trace k q := by
    have lifted := accessPositions_append_member (trace.take n) (trace.drop n) k q position member
    simpa only [List.take_append_drop] using lifted
  have firstBound := (firstAccess_spec trace k q accessed).2.2.2 position longMember
  have actualBound : position ≤ (trace.take n).length := by
    obtain ⟨pos, d, atPos, _, _, rfl⟩ := (mem_accessPositions_iff (trace.take n) k q position).mp member
    exact Nat.succ_le_of_lt (List.getElem?_eq_some_iff.mp atPos).choose
  exact Nat.le_trans firstBound (Nat.le_trans actualBound (List.length_take_le _ _))

/-- A pipeline initialization precedes every actual first access of its component. -/
theorem pipeline_entry_lt_firstAccess (trace : Trace m h executor prog) (entry slot : Nat)
    (q : sig.Path) (accessed : q ∈ componentAccesses trace (.pipeline entry slot)) :
    entry < firstAccess trace (.pipeline entry slot) q accessed := by
  have first := (firstAccess_spec trace (.pipeline entry slot) q accessed).1
  obtain ⟨pos, d, _, component, _, equal⟩ := (mem_accessPositions_iff trace _ q _).mp first
  rw [equal]
  exact Nat.lt_succ_of_le (componentAt_pipeline_entry_le trace pos d component)

/-- Equal access sets at every prefix give identical first accesses for matching pipeline components. -/
theorem matching_firstAccess {live : Trace m h .live prog} {vanilla : Trace m h .vanilla prog}
    (matched : List.Forall₂ MatchingProbeSteps live vanilla) (paths : PathsAtEveryPrefix live vanilla)
    (entry slot : Nat) (domain : .pipeline entry slot ∈ componentDomain live) (q : sig.Path)
    (leftAccess : q ∈ componentAccesses live (.pipeline entry slot))
    (rightAccess : q ∈ componentAccesses vanilla (.pipeline entry slot)) :
    firstAccess live (.pipeline entry slot) q leftAccess = firstAccess vanilla (.pipeline entry slot) q rightAccess := by
  have rightDomain : .pipeline entry slot ∈ componentDomain vanilla := by rwa [matching_componentDomain matched] at domain
  apply Nat.le_antisymm
  · let n := firstAccess vanilla (.pipeline entry slot) q rightAccess
    have nBound : n ≤ live.length := by
      rw [matched.length_eq]
      exact (firstAccess_spec vanilla _ q rightAccess).2.2.1
    have nEntry : entry < n := pipeline_entry_lt_firstAccess vanilla entry slot q rightAccess
    have rightIn : .pipeline entry slot ∈ componentDomain (vanilla.take n) := pipeline_domain_take vanilla entry slot n rightDomain nEntry
    have leftIn : .pipeline entry slot ∈ componentDomain (live.take n) := by
      rw [matching_componentDomain (List.forall₂_take n matched)]
      exact rightIn
    have rightHas : q ∈ componentAccesses (vanilla.take n) (.pipeline entry slot) :=
      accessPosition_take vanilla _ q n (firstAccess_spec vanilla _ q rightAccess).1 n (Nat.le_refl _)
    have leftHas : q ∈ componentAccesses (live.take n) (.pipeline entry slot) := by
      rw [(paths n nBound _ leftIn rightIn).2]
      exact rightHas
    exact access_take_implies_first_le live _ q leftAccess n leftHas
  · let n := firstAccess live (.pipeline entry slot) q leftAccess
    have nBound : n ≤ live.length := (firstAccess_spec live _ q leftAccess).2.2.1
    have nEntry : entry < n := pipeline_entry_lt_firstAccess live entry slot q leftAccess
    have leftIn : .pipeline entry slot ∈ componentDomain (live.take n) := pipeline_domain_take live entry slot n domain nEntry
    have rightIn : .pipeline entry slot ∈ componentDomain (vanilla.take n) := by
      rw [← matching_componentDomain (List.forall₂_take n matched)]
      exact leftIn
    have leftHas : q ∈ componentAccesses (live.take n) (.pipeline entry slot) :=
      accessPosition_take live _ q n (firstAccess_spec live _ q leftAccess).1 n (Nat.le_refl _)
    have rightHas : q ∈ componentAccesses (vanilla.take n) (.pipeline entry slot) := by
      rw [← (paths n nBound _ leftIn rightIn).2]
      exact leftHas
    exact access_take_implies_first_le vanilla _ q rightAccess n rightHas

/-- Equal every-prefix path sets include equal full-prefix sets for each present component. -/
theorem matching_full_paths {live : Trace m h .live prog} {vanilla : Trace m h .vanilla prog}
    (matched : List.Forall₂ MatchingProbeSteps live vanilla) (paths : PathsAtEveryPrefix live vanilla)
    (k : Component) (domain : k ∈ componentDomain live) :
    componentWrites live k = componentWrites vanilla k ∧ componentAccesses live k = componentAccesses vanilla k := by
  have otherDomain : k ∈ componentDomain vanilla := by rwa [matching_componentDomain matched] at domain
  have full := paths live.length (Nat.le_refl _) k (by simpa using domain)
    (by simpa [matched.length_eq] using otherDomain)
  have rightTake : vanilla.take live.length = vanilla := by rw [matched.length_eq, List.take_length]
  simpa only [List.take_length, rightTake] using full

/-- Exit ordering transfers in both directions from matched positions and every-prefix path sets. -/
theorem matching_exitOrdered {live : Trace m h .live prog} {vanilla : Trace m h .vanilla prog}
    (matched : List.Forall₂ MatchingProbeSteps live vanilla) (paths : PathsAtEveryPrefix live vanilla) :
    ExitOrdered live ↔ ExitOrdered vanilla := by
  constructor
  · intro ordered entry i j domainI domainJ different q shared
    have leftI : .pipeline entry i ∈ componentDomain live := by rwa [matching_componentDomain matched]
    have leftJ : .pipeline entry j ∈ componentDomain live := by rwa [matching_componentDomain matched]
    have writeEq := (matching_full_paths matched paths (.pipeline entry i) leftI).1
    have accessEq := (matching_full_paths matched paths (.pipeline entry j) leftJ).2
    have leftShared : q ∈ componentWrites live (.pipeline entry i) ∩
        componentAccesses live (.pipeline entry j) := by
      rw [writeEq, accessEq]
      exact shared
    have relation := ordered entry i j leftI leftJ different q leftShared
    have firstJ := matching_firstAccess matched paths entry j leftJ q leftShared.2 shared.2
    have firstI := matching_firstAccess matched paths entry i leftI q (Or.inr leftShared.1) (Or.inr shared.1)
    rw [matching_lastPosition matched (.pipeline entry i), matching_lastPosition matched (.pipeline entry j),
      firstJ, firstI] at relation
    exact relation
  · intro ordered entry i j domainI domainJ different q shared
    have rightI : .pipeline entry i ∈ componentDomain vanilla := by rwa [← matching_componentDomain matched]
    have rightJ : .pipeline entry j ∈ componentDomain vanilla := by rwa [← matching_componentDomain matched]
    have writeEq := (matching_full_paths matched paths (.pipeline entry i) domainI).1
    have accessEq := (matching_full_paths matched paths (.pipeline entry j) domainJ).2
    have rightShared : q ∈ componentWrites vanilla (.pipeline entry i) ∩
        componentAccesses vanilla (.pipeline entry j) := by
      rw [← writeEq, ← accessEq]
      exact shared
    have relation := ordered entry i j rightI rightJ different q rightShared
    have firstJ := matching_firstAccess matched paths entry j domainJ q shared.2 rightShared.2
    have firstI := matching_firstAccess matched paths entry i domainI q (Or.inr shared.1) (Or.inr rightShared.1)
    rw [← matching_lastPosition matched (.pipeline entry i), ← matching_lastPosition matched (.pipeline entry j),
      ← firstJ, ← firstI] at relation
    exact relation

/-- A new step adds its patch domain only to its actual component. -/
theorem componentWrites_snoc (trace : Trace m h executor prog) (d : StepDerivation m h executor prog)
    (k : Component) : componentWrites (trace ++ [d]) k =
      if componentAt (trace ++ [d]) trace.length d = some k then
        componentWrites trace k ∪ FMap.dom (ProbeDerivation.result d.probe).patch else componentWrites trace k := by
  classical
  by_cases same : componentAt (trace ++ [d]) trace.length d = some k
  · ext q
    simp [componentWrites, componentSteps_snoc, same]
  · ext q
    simp [componentWrites, componentSteps_snoc, same]

/-- A new step adds exactly its actual result accesses to its component. -/
theorem componentAccesses_snoc (trace : Trace m h executor prog) (d : StepDerivation m h executor prog)
    (k : Component) : componentAccesses (trace ++ [d]) k =
      if componentAt (trace ++ [d]) trace.length d = some k then
        componentAccesses trace k ∪ d.accesses else componentAccesses trace k := by
  classical
  by_cases same : componentAt (trace ++ [d]) trace.length d = some k
  · ext q
    simp only [componentAccesses, componentDeps, componentWrites, StepDerivation.accesses,
      componentSteps_snoc, same, ite_true, Set.mem_union, Set.mem_ofPred_eq,
      List.mem_append, List.mem_singleton, or_and_right, exists_or, exists_eq_left]
    aesop
  · ext q
    simp [componentAccesses, componentDeps, componentWrites, componentSteps_snoc, same]

/-- Every actual operational component step belongs to an initialized component domain. -/
theorem Operational.componentAt_mem_domain {start : World sig} (host : HostWellFormed m h)
    (pre : Prefix m h executor prog start) (operational : Operational pre)
    (pos : Nat) (d : StepDerivation m h executor prog) (k : Component)
    (atPos : (pre.trace)[pos]? = some d) (component : componentAt pre.trace pos d = some k) :
    k ∈ componentDomain pre.trace := by
  have bound := (List.getElem?_eq_some_iff.mp atPos).choose
  let short : Prefix m h executor prog start :=
    ⟨pre.trace.take pos, d.before, pre.initial, pre.connected.before_at atPos⟩
  have shortOperational := operational.of_trace_isPrefix (show short.trace.IsPrefix pre.trace from List.take_prefix _ _)
  have allowed : h.select prog short.final d.selection d.selected := d.host
  have shortLength : short.trace.length = pos := by
    simp [short, List.length_take, Nat.min_eq_left (Nat.le_of_lt bound)]
  have taken : pre.trace.take (pos + 1) = short.trace ++ [d] := by simp [short, List.take_add_one, atPos]
  have pref : (short.trace ++ [d]).IsPrefix pre.trace := by rw [← taken]; exact List.take_prefix _ _
  obtain ⟨extra, joined⟩ := pref
  have selected : componentAt (short.trace ++ [d]) short.trace.length d = some k := by
    rw [shortLength]
    have same : componentAt pre.trace pos d = componentAt (short.trace ++ [d]) pos d := by
      rw [← joined]
      exact componentAt_append _ _ pos d (by simp [shortLength])
    rw [← same]
    exact component
  have inShort : k ∈ componentDomain (short.trace ++ [d]) := by
    cases head : d.selection.head with
    | standalone p =>
      have named : componentAt (short.trace ++ [d]) short.trace.length d =
          some (.standalone short.trace.length) := by simp [componentAt_snoc, head]
      rw [named] at selected
      cases Option.some.inj selected
      apply (componentDomain_snoc short.trace d _).mpr
      exact Or.inr (Or.inl ⟨p, head, rfl⟩)
    | pipeline p slot =>
      have allocation := Operational.slotAllocation host short shortOperational (.selected d.selection d.selected allowed)
      have buffer := ProbeDerivation.pipeline_buffer_present (head ▸ d.probe)
      change slot ∈ FMap.dom (Boundary.selected d.selection d.selected allowed).world.buffer at buffer
      rw [allocation.buffers] at buffer
      obtain ⟨entry, current, domain, unclosed⟩ := buffer
      have named : componentAt (short.trace ++ [d]) short.trace.length d = some (.pipeline entry slot) := by
        rw [Boundary.componentAt_selected short d allowed head, current]
        rfl
      rw [named] at selected
      cases Option.some.inj selected
      exact (Boundary.pipelineDomain_snoc short d allowed entry slot).mpr domain
  rw [← joined]
  exact componentDomain_append_subset _ extra inShort

/-- A component outside an operational domain has no retained steps or paths. -/
theorem Operational.absent_component_paths {start : World sig} (host : HostWellFormed m h)
    (pre : Prefix m h executor prog start) (operational : Operational pre) (k : Component)
    (absent : k ∉ componentDomain pre.trace) :
    componentWrites pre.trace k = ∅ ∧ componentAccesses pre.trace k = ∅ := by
  have noSteps : componentSteps pre.trace k = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro d member
    obtain ⟨pos, atPos, component⟩ := (mem_componentSteps_iff pre.trace k d).mp member
    exact absent (Operational.componentAt_mem_domain host pre operational pos d k atPos component)
  constructor <;> ext q <;> simp [componentWrites, componentAccesses, componentDeps, noSteps]

/-- E.9's conditional path clause implies equal full path sets for every component. -/
theorem Correspondence.all_component_paths {start : World sig} (host : HostWellFormed m h)
    {context : PrefixContext m h prog start}
    {live : Prefix m h .live prog start} {vanilla : Prefix m h .vanilla prog start}
    (related : Correspondence context live vanilla) (k : Component) :
    componentWrites live.trace k = componentWrites vanilla.trace k ∧
      componentAccesses live.trace k = componentAccesses vanilla.trace k := by
  by_cases member : k ∈ componentDomain live.trace
  · exact matching_full_paths related.matchingSteps related.paths k member
  · have absent : k ∉ componentDomain vanilla.trace := by rwa [← matching_componentDomain related.matchingSteps]
    have left := Operational.absent_component_paths host live related.liveAdmissible.operational k member
    have right := Operational.absent_component_paths host vanilla related.vanillaAdmissible.operational k absent
    rw [left.1, left.2, right.1, right.2]
    exact ⟨rfl, rfl⟩

/-- One matched step preserves every-prefix path equality when its component's cumulative unions agree. -/
theorem Correspondence.paths_snoc {start : World sig} (host : HostWellFormed m h)
    {context : PrefixContext m h prog start}
    {live : Prefix m h .live prog start} {vanilla : Prefix m h .vanilla prog start}
    (related : Correspondence context live vanilla)
    (left : StepDerivation m h .live prog) (right : StepDerivation m h .vanilla prog)
    (step : MatchingProbeSteps left right)
    (newPaths : ∀ k, componentAt (live.trace ++ [left]) live.trace.length left = some k →
      (componentWrites live.trace k ∪ FMap.dom (ProbeDerivation.result left.probe).patch =
        componentWrites vanilla.trace k ∪ FMap.dom (ProbeDerivation.result right.probe).patch) ∧
      (componentAccesses live.trace k ∪ left.accesses = componentAccesses vanilla.trace k ∪ right.accesses)) :
    PathsAtEveryPrefix (live.trace ++ [left]) (vanilla.trace ++ [right]) := by
  have matched : List.Forall₂ MatchingProbeSteps (live.trace ++ [left]) (vanilla.trace ++ [right]) :=
    List.rel_append related.matchingSteps (List.Forall₂.cons step List.Forall₂.nil)
  have componentEq : componentAt (live.trace ++ [left]) live.trace.length left =
      componentAt (vanilla.trace ++ [right]) vanilla.trace.length right := by
    have equal := matching_componentAt matched live.trace.length left right step
    simpa only [related.length] using equal
  have full : ∀ k, componentWrites (live.trace ++ [left]) k = componentWrites (vanilla.trace ++ [right]) k ∧
      componentAccesses (live.trace ++ [left]) k = componentAccesses (vanilla.trace ++ [right]) k := by
    intro k
    have old := related.all_component_paths host k
    by_cases same : componentAt (live.trace ++ [left]) live.trace.length left = some k
    · have other : componentAt (vanilla.trace ++ [right]) vanilla.trace.length right = some k := componentEq.symm.trans same
      have addition := newPaths k same
      simp only [componentWrites_snoc, componentAccesses_snoc, same, other, ite_true]
      exact addition
    · have other : componentAt (vanilla.trace ++ [right]) vanilla.trace.length right ≠ some k := by
        intro equal
        exact same (componentEq.trans equal)
      simp only [componentWrites_snoc, componentAccesses_snoc, same, other, ite_false]
      exact old
  intro j bound k leftDomain rightDomain
  by_cases old : j ≤ live.trace.length
  · have oldRight : j ≤ vanilla.trace.length := by rwa [← related.length]
    simp only [List.take_append_of_le_length old, List.take_append_of_le_length oldRight] at leftDomain rightDomain ⊢
    exact related.paths j old k leftDomain rightDomain
  · have atEnd : j = (live.trace ++ [left]).length := by
      simp only [List.length_append, List.length_singleton] at bound ⊢
      omega
    have equalLength : (live.trace ++ [left]).length = (vanilla.trace ++ [right]).length := matched.length_eq
    rw [atEnd, List.take_length]
    rw [equalLength, List.take_length]
    exact full k

/-- Matched actual results with equal effect domains preserve every-prefix path sets. -/
theorem Correspondence.paths_snoc_equal_effects {start : World sig} (host : HostWellFormed m h)
    {context : PrefixContext m h prog start}
    {live : Prefix m h .live prog start} {vanilla : Prefix m h .vanilla prog start}
    (related : Correspondence context live vanilla)
    (left : StepDerivation m h .live prog) (right : StepDerivation m h .vanilla prog)
    (step : MatchingProbeSteps left right)
    (patch : FMap.dom (ProbeDerivation.result left.probe).patch = FMap.dom (ProbeDerivation.result right.probe).patch)
    (reads : FMap.dom (ProbeDerivation.result left.probe).reads = FMap.dom (ProbeDerivation.result right.probe).reads)
    (writes : FMap.dom (ProbeDerivation.result left.probe).writes = FMap.dom (ProbeDerivation.result right.probe).writes) :
    PathsAtEveryPrefix (live.trace ++ [left]) (vanilla.trace ++ [right]) := by
  apply related.paths_snoc host left right step
  intro k selected
  have old := related.all_component_paths host k
  constructor
  · rw [old.1, patch]
  · rw [old.2]
    unfold StepDerivation.accesses
    rw [patch, reads, writes]

/-- A pipeline hit's printed cumulative path equations preserve every-prefix path sets. -/
theorem Correspondence.paths_snoc_hit {start : World sig} (host : HostWellFormed m h)
    {context : PrefixContext m h prog start}
    {live : Prefix m h .live prog start} {vanilla : Prefix m h .vanilla prog start}
    (related : Correspondence context live vanilla)
    (left : StepDerivation m h .live prog) (right : StepDerivation m h .vanilla prog)
    (step : MatchingProbeSteps left right) (entry slot : Nat)
    (atComponent : componentAt (live.trace ++ [left]) live.trace.length left = some (.pipeline entry slot))
    (writePaths : componentWrites live.trace (.pipeline entry slot) ∪ FMap.dom (ProbeDerivation.result left.probe).patch =
      componentWrites live.trace (.pipeline entry slot) ∪ FMap.dom (ProbeDerivation.result right.probe).patch)
    (accessPaths : componentAccesses live.trace (.pipeline entry slot) ∪ left.accesses =
      componentAccesses live.trace (.pipeline entry slot) ∪ right.accesses) :
    PathsAtEveryPrefix (live.trace ++ [left]) (vanilla.trace ++ [right]) := by
  apply related.paths_snoc host left right step
  intro k selected
  rw [atComponent] at selected
  cases Option.some.inj selected
  have old := related.all_component_paths host (.pipeline entry slot)
  rw [← old.1, ← old.2]
  exact ⟨writePaths, accessPaths⟩

/-- Every operational vanilla endpoint retains the initial cache exactly. -/
theorem Operational.vanilla_cache {start : World sig} (host : HostWellFormed m h)
    (pre : Prefix m h .vanilla prog start) (operational : Operational pre) : pre.final.cache = start.cache := by
  apply Operational.snoc_induction (fun pre => pre.final.cache = start.cache) ?_ ?_ pre operational
  · intro pre _ empty
    have connected := pre.connected
    rw [empty] at connected
    have endpoint := (Connected.nil_iff start pre.final).mp connected
    rw [endpoint]
  · intro short post d shortOperational _ joined before after ih
    have allowed : h.select prog short.final d.selection d.selected := by simpa only [before] using d.host
    have discipline := host.selectionDiscipline .vanilla prog start short shortOperational d.selection d.selected allowed
    rw [after, d.probe.cache_unchanged, discipline.2.2.1, ih]

/-- E.4 and E.6 supply the entire E.9 cache and sandbox clause for matched endpoints. -/
theorem CacheAndSandboxes.of_endpoints {start : World sig}
    (shape : DenotationShape m) (commands : WellFormedCommands m) (host : HostWellFormed m h)
    (hash : HashInjective m) (context : PrefixContext m h prog start)
    (live : Prefix m h .live prog start) (vanilla : Prefix m h .vanilla prog start)
    (liveAdmissible : Admissible context.witnesses live) (vanillaAdmissible : Admissible context.witnesses vanilla)
    (control : ControlAgree live.final vanilla.final) : CacheAndSandboxes live vanilla := by
  have liveBuffers := buffer_properties host .live prog start live liveAdmissible.operational .final
  have vanillaBuffers := buffer_properties host .vanilla prog start vanilla vanillaAdmissible.operational .final
  have liveHistory := live_buffer_properties host prog start live liveAdmissible.operational .final
  have prefixes := prefixes_and_cache_preservation shape commands host hash live liveAdmissible.operational
    liveAdmissible.ordered context.cache context.witnesses context.chosen .final
  refine ⟨prefixes.cache, Operational.vanilla_cache host vanilla vanillaAdmissible.operational, ?_, ?_, ?_⟩
  · have leftEq : FMap.dom live.final.sandbox = FMap.dom live.final.buffer := by
      simpa only [Boundary.world] using liveBuffers.sandbox.trans liveBuffers.buffer.symm
    have rightEq : FMap.dom vanilla.final.sandbox = FMap.dom vanilla.final.buffer := by
      simpa only [Boundary.world] using vanillaBuffers.sandbox.trans vanillaBuffers.buffer.symm
    rw [leftEq, control.2.2.2.1, rightEq]
  · exact vanillaBuffers.vanillaEntries rfl
  · intro entry i sb liveEntry present
    exact ⟨liveBuffers.snapshots entry i sb liveEntry present,
      liveHistory entry i sb liveEntry present,
      fun p assigned cacheable => prefixes.entries entry i p sb liveEntry assigned cacheable present⟩

/-- Once both successors are admitted, matching controls, filesystem, and paths assemble E.9. -/
theorem Correspondence.snoc (shape : DenotationShape m) (commands : WellFormedCommands m)
    (host : HostWellFormed m h) (hash : HashInjective m) {start : World sig}
    {context : PrefixContext m h prog start}
    {live live' : Prefix m h .live prog start} {vanilla vanilla' : Prefix m h .vanilla prog start}
    (related : Correspondence context live vanilla)
    (left : StepDerivation m h .live prog) (right : StepDerivation m h .vanilla prog)
    (leftTrace : live'.trace = live.trace ++ [left]) (rightTrace : vanilla'.trace = vanilla.trace ++ [right])
    (step : MatchingProbeSteps left right) (liveAdmissible : Admissible context.witnesses live')
    (vanillaAdmissible : Admissible context.witnesses vanilla')
    (control : ControlAgree live'.final vanilla'.final) (filesystem : FSApprox live'.final.fs vanilla'.final.fs)
    (paths : PathsAtEveryPrefix live'.trace vanilla'.trace) : Correspondence context live' vanilla' := by
  have matched : List.Forall₂ MatchingProbeSteps live'.trace vanilla'.trace := by
    rw [leftTrace, rightTrace]
    exact List.rel_append related.matchingSteps (List.Forall₂.cons step List.Forall₂.nil)
  exact ⟨liveAdmissible, vanillaAdmissible, matched.length_eq, matched,
    CacheAndSandboxes.of_endpoints shape commands host hash context live' vanilla' liveAdmissible vanillaAdmissible control,
    filesystem, paths⟩

/-- Matched permitted selections retain control and filesystem approximation. -/
theorem Correspondence.selected_pair {start : World sig} (host : HostWellFormed m h)
    {context : PrefixContext m h prog start}
    {live : Prefix m h .live prog start} {vanilla : Prefix m h .vanilla prog start}
    (related : Correspondence context live vanilla) (control : ControlAgree live.final vanilla.final)
    (left : Selection sig) (lw : World sig) (leftAllowed : h.select prog live.final left lw)
    (right : Selection sig) (rw : World sig) (rightAllowed : h.select prog vanilla.final right rw)
    (matched : MatchingSelections left right lw rw) : ControlAgree lw rw ∧ FSApprox lw.fs rw.fs := by
  have leftLaw := host.selectionDiscipline .live prog start live related.liveAdmissible.operational left lw leftAllowed
  have rightLaw := host.selectionDiscipline .vanilla prog start vanilla related.vanillaAdmissible.operational right rw rightAllowed
  refine ⟨⟨matched.2.2.1, ?_, matched.2.2.2.1, matched.2.2.2.2.1, matched.2.2.2.2.2⟩, ?_⟩
  · exact leftLaw.2.1.trans (control.2.1.trans rightLaw.2.1.symm)
  · rw [leftLaw.1, rightLaw.1]
    exact related.filesystem

/-- Reindexing a retained vanilla derivation by an equal head preserves its result. -/
theorem VanillaDerivation.result_head_cast {before after : World sig} {left right : Head sig}
    {out : Option Chunk} (equal : left = right) (d : VanillaDerivation m before left after out) :
    VanillaDerivation.result (equal ▸ d) = VanillaDerivation.result d := by
  cases equal
  rfl

/-- Reindexing a retained live derivation by an equal head preserves its result. -/
theorem LiveDerivation.result_head_cast {before after : World sig} {left right : Head sig}
    {out : Option Chunk} (equal : left = right) (d : LiveDerivation m before left after out) :
    LiveDerivation.result (equal ▸ d) = LiveDerivation.result d := by
  cases equal
  rfl

/-- Reindexing a retained live derivation by an equal head preserves its call filesystem. -/
theorem LiveDerivation.callFS_head_cast {before after : World sig} {left right : Head sig}
    {out : Option Chunk} (equal : left = right) (d : LiveDerivation m before left after out) :
    LiveDerivation.callFS (equal ▸ d) = LiveDerivation.callFS d := by
  cases equal
  rfl

/-- An executing live edge has a fresh admitted vanilla edge preserving E.9. -/
theorem Correspondence.forward_executing {start : World sig}
    (commands : WellFormedCommands m) (shape : DenotationShape m) (host : HostWellFormed m h)
    (hash : HashInjective m) {context : PrefixContext m h prog start}
    {live live' : Prefix m h .live prog start} {vanilla : Prefix m h .vanilla prog start}
    (related : Correspondence context live vanilla) (control : ControlAgree live.final vanilla.final)
    (d : StepDerivation m h .live prog) (before : d.before = live.final)
    (joined : live'.trace = live.trace ++ [d]) (after : live'.final = d.after)
    (liveAdmissible : Admissible context.witnesses live')
    (executing : LiveDerivation.callFS d.probe = some d.selected.fs) :
    ∃ vanilla' : Prefix m h .vanilla prog start,
      PrefixStep context.witnesses d.selection.head vanilla vanilla' ∧ Correspondence context live' vanilla' := by
  have allowed : h.select prog live.final d.selection d.selected := by simpa only [before] using d.host
  obtain ⟨selection, world, chosen, matched⟩ :=
    (related.selection_transport host control).1 d.selection d.selected allowed
  have selectedPair := related.selected_pair host control d.selection d.selected allowed selection world chosen matched
  obtain ⟨vafter, vd, afterControl, inputEq, statusEq, outputEq, writesEq, readsEq,
    patchEq, fsEq, freshLocal, freshRecords⟩ :=
    d.probe.match_executing commands executing selectedPair.1 selectedPair.2
      (vanilla.records ++ witnessRecords context.witnesses)
  let targetProbe : VanillaDerivation m world selection.head vafter d.out := matched.1 ▸ vd
  have targetResult : VanillaDerivation.result targetProbe = VanillaDerivation.result vd :=
    VanillaDerivation.result_head_cast matched.1 vd
  let target : StepDerivation m h .vanilla prog :=
    ⟨vanilla.final, selection, world, vafter, d.out, chosen, targetProbe⟩
  let vanilla' : Prefix m h .vanilla prog start :=
    ⟨vanilla.trace ++ [target], vafter, vanilla.initial,
      (Connected.snoc_iff vanilla.trace target start vafter).mpr ⟨vanilla.connected, rfl⟩⟩
  have stepMatch : MatchingProbeSteps d target := by
    exact ⟨matched.1, rfl, selectedPair.1, afterControl, matched.2.1⟩
  have paths : PathsAtEveryPrefix live'.trace vanilla'.trace := by
    rw [joined]
    apply related.paths_snoc_equal_effects host d target stepMatch
    · simpa only [ProbeDerivation.result, target, targetResult] using patchEq.1.symm
    · simpa only [ProbeDerivation.result, target, targetResult] using readsEq.symm
    · simpa only [ProbeDerivation.result, target, targetResult] using congrArg FMap.dom writesEq.symm
  have targetOperational : Operational vanilla' ∧
      TimestampCompatible (vanilla'.records ++ witnessRecords context.witnesses) := by
    apply Operational.vanilla_snoc_fresh host vanilla vanilla' related.vanillaAdmissible.operational
      context.witnesses related.vanillaAdmissible.normalizedWitnesses target rfl rfl
    · simpa only [target, targetResult] using freshLocal
    · simpa only [target, targetResult] using freshRecords
  have newMatched : List.Forall₂ MatchingProbeSteps live'.trace vanilla'.trace := by
    rw [joined]
    exact List.rel_append related.matchingSteps (List.Forall₂.cons stepMatch List.Forall₂.nil)
  have targetOrdered : ExitOrdered vanilla'.trace :=
    (matching_exitOrdered newMatched paths).mp liveAdmissible.ordered
  have targetAdmissible : Admissible context.witnesses vanilla' :=
    ⟨targetOperational.1, targetOrdered,
      (vanilla'.paperRecords_witness_consistent_iff context.witnesses).mpr targetOperational.2⟩
  have endControl : ControlAgree live'.final vanilla'.final := by simpa only [after, vanilla'] using afterControl
  have endFS : FSApprox live'.final.fs vanilla'.final.fs := by simpa only [after, vanilla'] using fsEq
  have correspondence := related.snoc shape commands host hash d target joined rfl stepMatch liveAdmissible
    targetAdmissible endControl endFS paths
  refine ⟨vanilla', ⟨related.vanillaAdmissible, targetAdmissible, target, rfl, ?_, rfl, rfl⟩, correspondence⟩
  exact matched.1.symm

/-- Every vanilla edge has a fresh admitted live miss or uncacheable edge preserving E.9. -/
theorem Correspondence.backward_executing {start : World sig}
    (commands : WellFormedCommands m) (shape : DenotationShape m) (host : HostWellFormed m h)
    (hash : HashInjective m) {context : PrefixContext m h prog start}
    {live : Prefix m h .live prog start} {vanilla vanilla' : Prefix m h .vanilla prog start}
    (related : Correspondence context live vanilla) (control : ControlAgree live.final vanilla.final)
    (d : StepDerivation m h .vanilla prog) (before : d.before = vanilla.final)
    (joined : vanilla'.trace = vanilla.trace ++ [d]) (after : vanilla'.final = d.after)
    (vanillaAdmissible : Admissible context.witnesses vanilla') :
    ∃ live' : Prefix m h .live prog start,
      PrefixStep context.witnesses d.selection.head live live' ∧ Correspondence context live' vanilla' := by
  have allowed : h.select prog vanilla.final d.selection d.selected := by simpa only [before] using d.host
  obtain ⟨selection, world, chosen, reverseMatched⟩ :=
    (related.selection_transport host control).2 d.selection d.selected allowed
  have matched : MatchingSelections selection d.selection world d.selected :=
    ⟨reverseMatched.1.symm, reverseMatched.2.1.symm, reverseMatched.2.2.1.symm,
      reverseMatched.2.2.2.1.symm, reverseMatched.2.2.2.2.1.symm, reverseMatched.2.2.2.2.2.symm⟩
  have selectedPair := related.selected_pair host control selection world chosen d.selection d.selected allowed matched
  have sandbox : ∀ p i, d.selection.head = .pipeline p i → ∃ sb, FMap.get world.sandbox i = some sb ∧
      sb.input.flag = .open ∧ sb.output.flag = .open := by
    intro p i head
    apply Boundary.selected_open_sandbox shape host live related.liveAdmissible.operational selection world chosen p i
    exact matched.1.trans head
  obtain ⟨lafter, ld, afterControl, inputEq, statusEq, outputEq, writesEq, readsEq,
    patchEq, fsEq, executing, freshLocal, freshRecords⟩ :=
    d.probe.match_live shape commands selectedPair.1 selectedPair.2 sandbox (live.records ++ witnessRecords context.witnesses)
  let targetProbe : LiveDerivation m world selection.head lafter d.out := matched.1.symm ▸ ld
  have targetResult : LiveDerivation.result targetProbe = LiveDerivation.result ld :=
    LiveDerivation.result_head_cast matched.1.symm ld
  have targetCallFS : LiveDerivation.callFS targetProbe = LiveDerivation.callFS ld :=
    LiveDerivation.callFS_head_cast matched.1.symm ld
  let target : StepDerivation m h .live prog :=
    ⟨live.final, selection, world, lafter, d.out, chosen, targetProbe⟩
  let live' : Prefix m h .live prog start :=
    ⟨live.trace ++ [target], lafter, live.initial,
      (Connected.snoc_iff live.trace target start lafter).mpr ⟨live.connected, rfl⟩⟩
  have stepMatch : MatchingProbeSteps target d := by
    exact ⟨matched.1, rfl, selectedPair.1, afterControl, matched.2.1⟩
  have paths : PathsAtEveryPrefix live'.trace vanilla'.trace := by
    rw [joined]
    apply related.paths_snoc_equal_effects host target d stepMatch
    · simpa only [ProbeDerivation.result, target, targetResult] using patchEq.1
    · simpa only [ProbeDerivation.result, target, targetResult] using readsEq
    · simpa only [ProbeDerivation.result, target, targetResult] using congrArg FMap.dom writesEq
  have targetOperational : Operational live' ∧
      TimestampCompatible (live'.records ++ witnessRecords context.witnesses) := by
    apply Operational.live_snoc_fresh host live live' related.liveAdmissible.operational
      context.witnesses related.liveAdmissible.normalizedWitnesses target rfl rfl
    · simpa only [target, targetCallFS] using executing
    · simpa only [target, targetResult] using freshLocal
    · simpa only [target, targetResult] using freshRecords
  have newMatched : List.Forall₂ MatchingProbeSteps live'.trace vanilla'.trace := by
    rw [joined]
    exact List.rel_append related.matchingSteps (List.Forall₂.cons stepMatch List.Forall₂.nil)
  have targetOrdered : ExitOrdered live'.trace :=
    (matching_exitOrdered newMatched paths).mpr vanillaAdmissible.ordered
  have targetAdmissible : Admissible context.witnesses live' :=
    ⟨targetOperational.1, targetOrdered,
      (live'.paperRecords_witness_consistent_iff context.witnesses).mpr targetOperational.2⟩
  have endControl : ControlAgree live'.final vanilla'.final := by simpa only [after, live'] using afterControl
  have endFS : FSApprox live'.final.fs vanilla'.final.fs := by simpa only [after, live'] using fsEq
  have correspondence := related.snoc shape commands host hash target d rfl joined stepMatch targetAdmissible
    vanillaAdmissible endControl endFS paths
  refine ⟨live', ⟨related.liveAdmissible, targetAdmissible, target, rfl, ?_, rfl, rfl⟩, correspondence⟩
  exact matched.1

end
end IncrPP
end Incr
