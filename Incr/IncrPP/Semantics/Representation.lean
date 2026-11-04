import Incr.IncrPP.Semantics.Model

/-!
# Live representation obligations

These inverse laws certify the explicit state projections. They preserve
all fields without operational assumptions. They do not by themselves
establish paper exactness or complete the live soundness proof.
-/

namespace Incr.IncrPP

variable {sig : Signature}

/-- Projection and reconstruction retain every slot field. -/
theorem slotOfFields_slotFields (slot : Sandbox sig) :
    slotOfFields (slotFields slot) = slot := by
  rfl

/-- Every paper-shaped slot tuple is represented without additional data constraints. -/
theorem slotFields_slotOfFields (fields : SlotFields sig) :
    slotFields (slotOfFields fields) = fields := by
  rfl

/-- Projection and reconstruction retain every world field. -/
theorem worldOfFields_worldFields (world : World sig) :
    worldOfFields (worldFields world) = world := by
  rfl

/-- Every paper-shaped world tuple is represented. Operational conditions are separate. -/
theorem worldFields_worldOfFields (fields : WorldFields sig) :
    worldFields (worldOfFields fields) = fields := by
  rfl

end IncrPP
end Incr
