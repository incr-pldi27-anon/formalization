import Incr.IncrPP.Semantics.Views

/-!
# Actual slot-domain effects of the raw probe rules

Open calls retain the allocated source slot. EOF calls remove it. Routing
only changes an existing successor. Standalone calls frame both maps.
-/

namespace Incr.IncrPP

variable {sig : Signature} {m : CommandModel sig} {executor : Executor}

/-- Pipeline routing removes exactly its EOF-consuming source, and otherwise keeps the domain. -/
theorem ProbeDerivation.pipeline_buffers_domain {before after : World sig} {p : sig.Probe} {slot : Nat}
    {returned : Option Chunk} (d : ProbeDerivation m executor before (.pipeline p slot) after returned) :
    FMap.dom after.buffer = if (ProbeDerivation.input d).flag = .eof then
      {i | i ∈ FMap.dom before.buffer ∧ i ≠ slot} else FMap.dom before.buffer := by
  cases executor <;> cases d
  all_goals simp only [ProbeDerivation.input, LiveDerivation.input, VanillaDerivation.input,
    reduceCtorEq, ite_false, ite_true]
  case live.pipelineOpen =>
    exact (put_domain (by assumption)).trans (FMap.dom_set_of_get _ _ _ ⟨_, by assumption⟩)
  case vanilla.openStep =>
    exact (put_domain (by assumption)).trans (FMap.dom_set_of_get _ _ _ ⟨_, by assumption⟩)
  all_goals exact (put_domain (by assumption)).trans (FMap.dom_erase _ _)

/-- Sandbox domains have the identical open/EOF source-slot effect. -/
theorem ProbeDerivation.pipeline_sandboxes_domain {before after : World sig} {p : sig.Probe} {slot : Nat}
    {returned : Option Chunk} (d : ProbeDerivation m executor before (.pipeline p slot) after returned) :
    FMap.dom after.sandbox = if (ProbeDerivation.input d).flag = .eof then
      {i | i ∈ FMap.dom before.sandbox ∧ i ≠ slot} else FMap.dom before.sandbox := by
  cases executor <;> cases d
  all_goals simp only [ProbeDerivation.input, LiveDerivation.input, VanillaDerivation.input,
    reduceCtorEq, ite_false, ite_true]
  case live.pipelineOpen => exact FMap.dom_set_of_get _ _ _ ⟨_, by assumption⟩
  all_goals exact FMap.dom_erase _ _

/-- Every raw pipeline branch consumes an allocated buffer. -/
theorem ProbeDerivation.pipeline_buffer_present {before after : World sig} {p : sig.Probe} {slot : Nat}
    {returned : Option Chunk} (d : ProbeDerivation m executor before (.pipeline p slot) after returned) :
    slot ∈ FMap.dom before.buffer := by
  change slot ∈ before.buffer
  cases executor <;> cases d
  all_goals exact Finmap.mem_of_lookup_eq_some (by assumption)

/-- Standalone branches leave both allocation maps unchanged. -/
theorem ProbeDerivation.standalone_slots {before after : World sig} {p : sig.Probe}
    {returned : Option Chunk} (d : ProbeDerivation m executor before (.standalone p) after returned) :
    after.buffer = before.buffer ∧ after.sandbox = before.sandbox := by
  cases executor <;> cases d <;> exact ⟨rfl, rfl⟩

/-- A retained head equation exposes the buffer effect without replacing the derivation. -/
theorem ProbeDerivation.buffers_domain {before after : World sig} {head : Head sig}
    {returned : Option Chunk} (d : ProbeDerivation m executor before head after returned)
    {p : sig.Probe} {slot : Nat} (pipeline : head = .pipeline p slot) :
    FMap.dom after.buffer = if (ProbeDerivation.input d).flag = .eof then
      {i | i ∈ FMap.dom before.buffer ∧ i ≠ slot} else FMap.dom before.buffer := by
  subst head
  exact d.pipeline_buffers_domain

/-- The same retained derivation gives the corresponding sandbox-domain effect. -/
theorem ProbeDerivation.sandboxes_domain {before after : World sig} {head : Head sig}
    {returned : Option Chunk} (d : ProbeDerivation m executor before head after returned)
    {p : sig.Probe} {slot : Nat} (pipeline : head = .pipeline p slot) :
    FMap.dom after.sandbox = if (ProbeDerivation.input d).flag = .eof then
      {i | i ∈ FMap.dom before.sandbox ∧ i ≠ slot} else FMap.dom before.sandbox := by
  subst head
  exact d.pipeline_sandboxes_domain

/-- A standalone head equation exposes the same map frame on the original derivation. -/
theorem ProbeDerivation.slots_of_standalone {before after : World sig} {head : Head sig}
    {returned : Option Chunk} (d : ProbeDerivation m executor before head after returned)
    {p : sig.Probe} (standalone : head = .standalone p) :
    after.buffer = before.buffer ∧ after.sandbox = before.sandbox := by
  subst head
  exact d.standalone_slots

/-- A pipeline judgment consumes input with the flag of its selected buffer. -/
theorem ProbeDerivation.pipeline_buffer_flag {before after : World sig} {head : Head sig}
    {returned : Option Chunk} (d : ProbeDerivation m executor before head after returned)
    {p : sig.Probe} {slot : Nat} (pipeline : head = .pipeline p slot) :
    ∃ chunk, FMap.get before.buffer slot = some chunk ∧ chunk.flag = (ProbeDerivation.input d).flag := by
  subst head
  cases executor <;> cases d
  case live.pipelineOpen =>
    rename_i sb taken remaining r buffers hinput houtput hstatus hflag hcall hbuffer hsandbox hput
    exact ⟨⟨taken ++ remaining, .open⟩, hbuffer, rfl⟩
  case vanilla.openStep =>
    rename_i taken remaining r buffers hstatus hflag hcall hbuffer hput
    exact ⟨⟨taken ++ remaining, .open⟩, hbuffer, rfl⟩
  all_goals exact ⟨_, by assumption, rfl⟩

end IncrPP
end Incr
