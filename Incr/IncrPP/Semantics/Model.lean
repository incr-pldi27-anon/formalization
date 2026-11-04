import Incr.Assumptions.Commands

/-!
# Shared data and explicit live-state projections

Appendix E retains the same world and six-field slot entry as the shared
model. A slot's captured base is historical data, not the filesystem read by
live calls. The projections below expose the printed tuples directly.

Only shared data, model predicates, and command assumptions are imported.
No Incr 1.0 rule, host contract, trace, or proof is imported.
-/

namespace Incr.IncrPP

variable {sig : Signature}

/-- The six fields of the paper's slot entry, in printed order. -/
abbrev SlotFields (sig : Signature) :=
  FS sig × Chunk × Reads sig × Writes sig × Patch sig × Chunk

/-- The semantic map from the shared typed slot to the paper tuple. -/
def slotFields (slot : Sandbox sig) : SlotFields sig :=
  ⟨slot.base, slot.input, slot.reads, slot.writes, slot.patch, slot.output⟩

/-- The inverse data map. No operational meaning is attached to the base. -/
def slotOfFields (fields : SlotFields sig) : Sandbox sig :=
  let ⟨base, input, reads, writes, patch, output⟩ := fields
  ⟨base, input, reads, writes, patch, output⟩

/-- The eight fields of the paper's world, in printed order. -/
abbrev WorldFields (sig : Signature) :=
  Nat × FS sig × Env sig × Cache sig × FMap Nat Chunk ×
    FMap Nat (Sandbox sig) × Chunk × sig.PC

/-- The semantic map from the shared typed world to the paper tuple. -/
def worldFields (world : World sig) : WorldFields sig :=
  ⟨world.ec, world.fs, world.env, world.cache, world.buffer,
    world.sandbox, world.stdin, world.pc⟩

/-- The inverse world-data map. -/
def worldOfFields (fields : WorldFields sig) : World sig :=
  let ⟨status, fs, env, cache, buffers, sandboxes, stdin, pc⟩ := fields
  ⟨status, fs, env, cache, buffers, sandboxes, stdin, pc⟩

/-- The two executor labels used by Appendix E. -/
inductive Executor where
  | live
  | vanilla
  deriving DecidableEq, Repr

end IncrPP
end Incr
