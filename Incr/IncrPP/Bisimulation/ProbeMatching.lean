import Incr.IncrPP.Preservation.BisimulationComponents

/-!
# Raw live and vanilla probe matching

These constructions use the independent live rule families. They retain
actual routing, consumed input, and output effects; they add no adapter to
the Incr 1.0 operational development.
-/

namespace Incr.IncrPP

noncomputable section

variable {sig : Signature} {m : CommandModel sig}

/-- A target call with the source step's status and produced output gives a vanilla step. -/
theorem LiveDerivation.to_vanilla {w v after : World sig} {head : Head sig} {out : Option Chunk}
    (d : LiveDerivation m w head after out) (control : ControlAgree w v)
    (r : Result sig) (call : m.denotes head.probe (LiveDerivation.input d) v.fs v.env r)
    (status : r.status = (LiveDerivation.result d).status)
    (output : r.output = LiveDerivation.produced d) :
    ∃ vafter, ∃ vd : VanillaDerivation m v head vafter out,
      ControlAgree after vafter ∧ VanillaDerivation.input vd = LiveDerivation.input d ∧
      VanillaDerivation.result vd = r := by
  obtain ⟨pc, oldStatus, env, buffersEq, stdinEq⟩ := control
  cases d
  all_goals dsimp only [Head.probe, LiveDerivation.input, LiveDerivation.result,
    LiveDerivation.produced, Memo.result] at call status output ⊢
  case pipelineOpen =>
    rename_i p i sb taken remaining original buffers hbuffer hsandbox hinput houtput hcall hstatus hflag hput
    refine ⟨_, .openStep v p i taken remaining r buffers _
      (by simpa only [← buffersEq] using hbuffer) call (status.trans hstatus)
      (by simpa only [output] using hflag) (by simpa only [updateBuffer, ← buffersEq, output] using hput), ?_⟩
    exact ⟨⟨pc, oldStatus, env, rfl, stdinEq⟩, rfl, rfl⟩
  case uncacheClose =>
    rename_i p i sb s original es buffers hcacheable hbuffer hsandbox hcall hstatus hflag hput
    refine ⟨_, .closeStep v p i s r es buffers _
      (by simpa only [← buffersEq] using hbuffer) call (status.trans hstatus)
      (by simpa only [output] using hflag) (by simpa only [← buffersEq, output] using hput), ?_⟩
    exact ⟨⟨pc, rfl, env, rfl, stdinEq⟩, rfl, rfl⟩
  case cacheCloseMiss =>
    rename_i p i sb s original es buffers cache hcacheable hbuffer hsandbox hinput houtput hcall hstatus hflag hcache hput
    refine ⟨_, .closeStep v p i s r es buffers _
      (by simpa only [← buffersEq] using hbuffer) call (status.trans hstatus)
      (by simpa only [output] using hflag) (by simpa only [closeBuffer, ← buffersEq, output] using hput), ?_⟩
    exact ⟨⟨pc, rfl, env, rfl, stdinEq⟩, rfl, rfl⟩
  case cacheCloseHit =>
    rename_i p i sb s tail memo applied buffers hcacheable hempty hbuffer hsandbox hinput houtput hmemo hvalid hguard hpatch hput
    refine ⟨_, .closeStep v p i s r memo.ec buffers _
      (by simpa only [← buffersEq] using hbuffer) call status
      (by simp only [output]) (by simpa only [closeBuffer, ← buffersEq, output] using hput), ?_⟩
    exact ⟨⟨pc, rfl, env, rfl, stdinEq⟩, rfl, rfl⟩
  case uncacheStandalone =>
    rename_i p s original es hcacheable hstdin hcall hstatus
    refine ⟨standaloneWorld v es r.patch, ?_, ?_⟩
    · rw [← output]
      exact .standalone v p s r es (by simpa only [← stdinEq] using hstdin) call (status.trans hstatus)
    · refine ⟨⟨pc, rfl, env, buffersEq, rfl⟩, ?_⟩
      cases r; cases original; dsimp at output; cases output; exact ⟨rfl, rfl⟩
  case cacheStandaloneMiss =>
    rename_i p s original es cache hcacheable hstdin hcall hstatus hflag hcache
    refine ⟨standaloneWorld v es r.patch, ?_, ?_⟩
    · rw [← output]
      exact .standalone v p s r es (by simpa only [← stdinEq] using hstdin) call (status.trans hstatus)
    · refine ⟨⟨pc, rfl, env, buffersEq, rfl⟩, ?_⟩
      cases r; cases original; dsimp at output; cases output; exact ⟨rfl, rfl⟩
  case cacheStandaloneHit =>
    rename_i p s memo applied hcacheable hstdin hmemo hvalid hpatch
    refine ⟨standaloneWorld v memo.ec r.patch, ?_, ?_⟩
    · rw [← output]
      exact .standalone v p s r memo.ec (by simpa only [← stdinEq] using hstdin) call status
    · refine ⟨⟨pc, rfl, env, buffersEq, rfl⟩, ?_⟩
      cases r; cases memo; dsimp at output; cases output; exact ⟨rfl, rfl⟩

/-- A transported vanilla call gives a live open or miss step with the same observed effects. -/
theorem VanillaDerivation.to_live (shape : DenotationShape m)
    {w v after : World sig} {head : Head sig} {out : Option Chunk}
    (d : VanillaDerivation m v head after out) (control : ControlAgree w v)
    (sandbox : ∀ p i, head = .pipeline p i → ∃ sb, FMap.get w.sandbox i = some sb ∧
      sb.input.flag = .open ∧ sb.output.flag = .open)
    (r : Result sig) (call : m.denotes head.probe (VanillaDerivation.input d) w.fs w.env r)
    (status : r.status = (VanillaDerivation.result d).status)
    (output : r.output = VanillaDerivation.produced d) :
    ∃ lafter, ∃ ld : LiveDerivation m w head lafter out,
      ControlAgree lafter after ∧ LiveDerivation.input ld = VanillaDerivation.input d ∧
      LiveDerivation.result ld = r ∧ LiveDerivation.callFS ld = some w.fs := by
  obtain ⟨pc, oldStatus, env, buffersEq, stdinEq⟩ := control
  cases d
  all_goals dsimp only [Head.probe, VanillaDerivation.input, VanillaDerivation.result,
    VanillaDerivation.produced] at call status output ⊢
  case openStep =>
    rename_i p i taken remaining original buffers hbuffer hcall hstatus hflag hput
    obtain ⟨sb, hsandbox, hin, hout⟩ := sandbox p i rfl
    refine ⟨_, .pipelineOpen w p i sb taken remaining r buffers _
      (by simpa only [buffersEq] using hbuffer) hsandbox hin hout call (status.trans hstatus)
      (by simpa only [output] using hflag) (by simpa only [updateBuffer, buffersEq, output] using hput), ?_⟩
    exact ⟨⟨pc, oldStatus, env, rfl, stdinEq⟩, rfl, rfl, rfl⟩
  case closeStep =>
    rename_i p i s original es buffers hbuffer hcall hstatus hflag hput
    obtain ⟨sb, hsandbox, hin, hout⟩ := sandbox p i rfl
    by_cases cacheable : Cacheable m p
    · let key := cacheKey m p w.env (Chunk.concat sb.input ⟨s, .eof⟩ hin)
      let memo := accumulatedMemo sb ⟨s, .eof⟩ r es hin hout (by simpa only [output] using hflag)
      refine ⟨_, .cacheCloseMiss w p i sb s r es buffers _ (FMap.set w.cache key memo) cacheable
        (by simpa only [buffersEq] using hbuffer) hsandbox hin hout call (status.trans hstatus)
        (by simpa only [output] using hflag) (Or.inl rfl)
        (by simpa only [closeBuffer, buffersEq, output] using hput), ?_⟩
      exact ⟨⟨pc, rfl, env, rfl, stdinEq⟩, rfl, rfl, rfl⟩
    · refine ⟨_, .uncacheClose w p i sb s r es buffers _ cacheable
        (by simpa only [buffersEq] using hbuffer) hsandbox call (status.trans hstatus)
        (by simpa only [output] using hflag) (by simpa only [buffersEq, output] using hput), ?_⟩
      exact ⟨⟨pc, rfl, env, rfl, stdinEq⟩, rfl, rfl, rfl⟩
  case standalone =>
    rename_i p s original es hstdin hcall hstatus
    have flag : r.output.flag = .eof := (shape p _ _ _ r call).2 rfl |>.1
    by_cases cacheable : Cacheable m p
    · let key := cacheKey m p w.env ⟨s, .eof⟩
      let memo : Memo sig := ⟨es, r.patch, r.reads, r.writes, r.output, flag⟩
      refine ⟨{ standaloneWorld w es r.patch with cache := FMap.set w.cache key memo }, ?_, ?_⟩
      · rw [← output]
        exact .cacheStandaloneMiss w p s r es (FMap.set w.cache key memo) cacheable
          (stdinEq.trans hstdin) call (status.trans hstatus) flag (Or.inl rfl)
      · refine ⟨⟨pc, rfl, env, buffersEq, rfl⟩, ?_⟩
        cases r; cases original; dsimp at output; cases output; exact ⟨rfl, rfl, rfl⟩
    · refine ⟨standaloneWorld w es r.patch, ?_, ?_⟩
      · rw [← output]
        exact .uncacheStandalone w p s r es cacheable (stdinEq.trans hstdin) call (status.trans hstatus)
      · refine ⟨⟨pc, rfl, env, buffersEq, rfl⟩, ?_⟩
        cases r; cases original; dsimp at output; cases output; exact ⟨rfl, rfl, rfl⟩

/-- Every non-hit live rule retains its actual denotation call. -/
theorem LiveDerivation.executing_call {w after : World sig} {head : Head sig} {out : Option Chunk}
    (d : LiveDerivation m w head after out) (executing : LiveDerivation.callFS d = some w.fs) :
    m.denotes head.probe (LiveDerivation.input d) w.fs w.env (LiveDerivation.result d) := by
  cases d <;> simp_all [LiveDerivation.callFS, LiveDerivation.input, LiveDerivation.result, Head.probe]

/-- Every vanilla rule retains its actual current-filesystem denotation call. -/
theorem VanillaDerivation.executing_call {w after : World sig} {head : Head sig} {out : Option Chunk}
    (d : VanillaDerivation m w head after out) :
    m.denotes head.probe (VanillaDerivation.input d) w.fs w.env (VanillaDerivation.result d) := by
  cases d <;> simp_all [VanillaDerivation.input, VanillaDerivation.result, Head.probe]

/-- Executing live rules produce the retained result output and apply its patch. -/
theorem LiveDerivation.executing_effects {w after : World sig} {head : Head sig} {out : Option Chunk}
    (d : LiveDerivation m w head after out) (executing : LiveDerivation.callFS d = some w.fs) :
    LiveDerivation.produced d = (LiveDerivation.result d).output ∧
      after.fs = applyPatch w.fs (LiveDerivation.result d).patch := by
  cases d <;> simp_all [LiveDerivation.callFS, LiveDerivation.produced, LiveDerivation.result,
    closeWorld, standaloneWorld]

/-- Every vanilla rule produces its retained result output and applies its patch. -/
theorem VanillaDerivation.executing_effects {w after : World sig} {head : Head sig} {out : Option Chunk}
    (d : VanillaDerivation m w head after out) :
    VanillaDerivation.produced d = (VanillaDerivation.result d).output ∧
      after.fs = applyPatch w.fs (VanillaDerivation.result d).patch := by
  cases d <;> simp [VanillaDerivation.produced, VanillaDerivation.result, closeWorld, standaloneWorld]

/-- Every executing live rule admits a fresh vanilla match on an approximate selected filesystem. -/
theorem LiveDerivation.match_executing {w v after : World sig} {head : Head sig} {out : Option Chunk}
    (commands : WellFormedCommands m) (d : LiveDerivation m w head after out)
    (executing : LiveDerivation.callFS d = some w.fs) (control : ControlAgree w v)
    (agreement : FSApprox w.fs v.fs) (records : Records sig) :
    ∃ vafter, ∃ vd : VanillaDerivation m v head vafter out,
      ControlAgree after vafter ∧ VanillaDerivation.input vd = LiveDerivation.input d ∧
      (VanillaDerivation.result vd).status = (LiveDerivation.result d).status ∧
      (VanillaDerivation.result vd).output = LiveDerivation.produced d ∧
      (VanillaDerivation.result vd).writes = (LiveDerivation.result d).writes ∧
      FMap.dom (VanillaDerivation.result vd).reads = FMap.dom (LiveDerivation.result d).reads ∧
      PatchApprox (VanillaDerivation.result vd).patch (LiveDerivation.result d).patch ∧
      FSApprox after.fs vafter.fs ∧ FreshPatch (VanillaDerivation.result vd).patch v.fs v.fs ∧
      ∀ q file, FMap.get (VanillaDerivation.result vd).patch q = some (.write file) →
        ∀ q' old, (q', old) ∈ records → file.mtime ≠ old.mtime := by
  have sourceCall := d.executing_call executing
  have effects := d.executing_effects executing
  obtain ⟨r, call, status, output, writes, reads, patch, fresh, outside⟩ :=
    transport_call_fresh commands head.probe (LiveDerivation.input d) w.fs v.fs v.fs w.env
      (LiveDerivation.result d) sourceCall agreement records
  have targetCall : m.denotes head.probe (LiveDerivation.input d) v.fs v.env r := by
    simpa only [control.2.2.1] using call
  obtain ⟨vafter, vd, afterControl, inputEq, resultEq⟩ := d.to_vanilla control r targetCall status (output.trans effects.1.symm)
  have targetEffect := vd.executing_effects
  refine ⟨vafter, vd, afterControl, inputEq, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [resultEq] using status
  · simpa only [resultEq] using output.trans effects.1.symm
  · simpa only [resultEq] using writes
  · simpa only [resultEq] using reads
  · simpa only [resultEq] using patch
  · rw [effects.2, targetEffect.2, resultEq]
    exact fsApprox_applyPatch agreement (patchApprox_symm patch)
  · simpa only [resultEq] using fresh
  · simpa only [resultEq] using outside

/-- Every vanilla rule admits a fresh live miss or uncacheable match. -/
theorem VanillaDerivation.match_live {w v after : World sig} {head : Head sig} {out : Option Chunk}
    (shape : DenotationShape m) (commands : WellFormedCommands m) (d : VanillaDerivation m v head after out)
    (control : ControlAgree w v) (agreement : FSApprox w.fs v.fs)
    (sandbox : ∀ p i, head = .pipeline p i → ∃ sb, FMap.get w.sandbox i = some sb ∧
      sb.input.flag = .open ∧ sb.output.flag = .open) (records : Records sig) :
    ∃ lafter, ∃ ld : LiveDerivation m w head lafter out,
      ControlAgree lafter after ∧ LiveDerivation.input ld = VanillaDerivation.input d ∧
      (LiveDerivation.result ld).status = (VanillaDerivation.result d).status ∧
      (LiveDerivation.result ld).output = VanillaDerivation.produced d ∧
      (LiveDerivation.result ld).writes = (VanillaDerivation.result d).writes ∧
      FMap.dom (LiveDerivation.result ld).reads = FMap.dom (VanillaDerivation.result d).reads ∧
      PatchApprox (LiveDerivation.result ld).patch (VanillaDerivation.result d).patch ∧
      FSApprox lafter.fs after.fs ∧ LiveDerivation.callFS ld = some w.fs ∧
      FreshPatch (LiveDerivation.result ld).patch w.fs w.fs ∧
      ∀ q file, FMap.get (LiveDerivation.result ld).patch q = some (.write file) →
        ∀ q' old, (q', old) ∈ records → file.mtime ≠ old.mtime := by
  have sourceCall := d.executing_call
  have effects := d.executing_effects
  have opposite : FSApprox v.fs w.fs := FSApprox.of_contents (fun q => (agreement.contents q).symm)
  obtain ⟨r, call, status, output, writes, reads, patch, fresh, outside⟩ :=
    transport_call_fresh commands head.probe (VanillaDerivation.input d) v.fs w.fs w.fs v.env
      (VanillaDerivation.result d) sourceCall opposite records
  have targetCall : m.denotes head.probe (VanillaDerivation.input d) w.fs w.env r := by
    simpa only [control.2.2.1] using call
  obtain ⟨lafter, ld, afterControl, inputEq, resultEq, executing⟩ :=
    d.to_live shape control sandbox r targetCall status (output.trans effects.1.symm)
  have targetEffects := ld.executing_effects executing
  refine ⟨lafter, ld, afterControl, inputEq, ?_, ?_, ?_, ?_, ?_, ?_, executing, ?_, ?_⟩
  · simpa only [resultEq] using status
  · simpa only [resultEq] using output.trans effects.1.symm
  · simpa only [resultEq] using writes
  · simpa only [resultEq] using reads
  · simpa only [resultEq] using patch
  · rw [targetEffects.2, effects.2, resultEq]
    exact fsApprox_applyPatch agreement patch
  · simpa only [resultEq] using fresh
  · simpa only [resultEq] using outside

variable {h : Host sig} {prog : sig.Prog} {start : World sig}

/-- Each permitted selected live pipeline head has an allocated open payload. -/
theorem Boundary.selected_open_sandbox (shape : DenotationShape m) (host : HostWellFormed m h)
    (pre : Prefix m h .live prog start) (operational : Operational pre)
    (selection : Selection sig) (world : World sig) (allowed : h.select prog pre.final selection world) :
    ∀ p i, selection.head = .pipeline p i → ∃ sb, FMap.get world.sandbox i = some sb ∧
      sb.input.flag = .open ∧ sb.output.flag = .open := by
  intro p i head
  have discipline := host.selectionDiscipline .live prog start pre operational selection world allowed
  have law := discipline.2.2.2.2
  rw [head] at law
  have present : i ∈ FMap.dom world.sandbox := law.2.2.1
  obtain ⟨sb, lookup⟩ := Finmap.mem_iff.mp (Finmap.mem_keys.mp present)
  change FMap.get world.sandbox i = some sb at lookup
  have allocation := Operational.slotAllocation host pre operational (.selected selection world allowed)
  have buffered : i ∈ (Boundary.selected selection world allowed).unclosedSlots := by
    rw [← allocation.sandboxes]
    exact present
  obtain ⟨entry, live⟩ := buffered
  have flags := Operational.liveOpenFlags shape host pre operational (.selected selection world allowed)
    entry i sb live lookup
  exact ⟨sb, lookup, flags⟩

end
end IncrPP
end Incr
