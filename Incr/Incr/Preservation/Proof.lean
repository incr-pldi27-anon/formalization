import Incr.Incr.Preservation.Order
import Incr.Incr.Preservation.Prefixes

/-! # `lem:paper-buffers` preservation and `lem:paper-sandbox` cacheable prefixes -/

open Incr
namespace Incr.Incr

variable {sig : Signature} {m : CommandModel sig} {h : Host sig}
  {prog : sig.Prog} {start : World sig}

/-- `lem:paper-buffers` (buffer and sandbox preservation): buffer and sandbox
preservation for either executor. -/
theorem buffer_sandbox_preservation {executor : Executor}
    (_shape : DenotationShape m) (_commands : WellFormedCommands m)
    (_key : HashInjective m) (_host : HostWellFormed m h)
    (pre : Prefix m h executor prog start) (_operational : Operational pre) :
    BufferSandboxPreservation pre := by
  exact BufferPreservation.preservation _shape _commands _key _host pre _operational

/-- `lem:paper-sandbox` (cacheable prefixes and cache preservation): cacheable
prefixes, `eq:paper-fold`, and cache preservation. -/
theorem cacheable_prefixes (_shape : DenotationShape m) (_commands : WellFormedCommands m)
    (_key : HashInjective m) (host : HostWellFormed m h)
    (_cache : WellFormedCache m start.cache)
    (pre : Prefix m h .incr prog start) (operational : Operational pre) :
    CacheablePrefixPreservation pre host operational := by
  obtain ⟨wf, prefixes⟩ := PrefixPreservation.joint_preservation _commands host _cache
    (fun earlier op => (buffer_sandbox_preservation _shape _commands _key host earlier op).1)
    pre operational
  exact ⟨wf, prefixes, CachePrefixes.next_call_folds _commands host operational
    (buffer_sandbox_preservation _shape _commands _key host pre operational).1 prefixes⟩

end Incr.Incr
