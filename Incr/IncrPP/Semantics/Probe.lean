import Incr.IncrPP.Semantics.Rules
import Incr.IncrPP.Semantics.Vanilla

/-!
# Executor-indexed raw live judgments

The index distinguishes Appendix E's live and vanilla-live rules. It does
not identify either executor with the Incr 1.0 operational system.
-/

namespace Incr.IncrPP

variable {sig : Signature}

/-- Keep the chosen raw derivation rather than erase it to a proposition. -/
def ProbeDerivation (m : CommandModel sig) (executor : Executor) :
    World sig → Head sig → World sig → Option Chunk → Type :=
  match executor with
  | .live => LiveDerivation m
  | .vanilla => VanillaDerivation m

/-- The existential indexed probe judgment. -/
def ProbeStep (m : CommandModel sig) (executor : Executor)
    (before : World sig) (head : Head sig) (after : World sig) (out : Option Chunk) : Prop :=
  Nonempty (ProbeDerivation m executor before head after out)

end IncrPP
end Incr
