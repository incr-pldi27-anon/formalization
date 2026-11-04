import Incr.IncrPP.Semantics.Model

/-!
# Abstract live host data

The same live selection and completion relations serve both live executors.
This module states no host well-formedness law and imports no sandbox host.
Initialization and delivery fields retain witnesses; observations must use
world effects rather than compare whole annotation records.
-/

namespace Incr.IncrPP

variable {sig : Signature}

/-- Ordered probe assignment and entry input at a pipeline initialization. -/
structure PipelineInit (sig : Signature) where
  probes : List sig.Probe
  input : Chunk

/-- A selected probe and its retained initialization or delivery annotation. -/
structure Selection (sig : Signature) where
  head : Head sig
  init : Option (PipelineInit sig)
  delivery : Option Chunk

/-- Abstract initial control, live host selection, and live completion. -/
structure Host (sig : Signature) where
  initialControl : sig.Prog → sig.PC → Nat → Prop
  select : sig.Prog → World sig → Selection sig → World sig → Prop
  complete : sig.Prog → World sig → Prop

/-- Initial worlds have no allocated pipeline or pending standalone input. -/
def Initial (h : Host sig) (prog : sig.Prog) (w : World sig) : Prop :=
  w.buffer = ∅ ∧ w.sandbox = ∅ ∧ w.stdin = .emptyEOF ∧
    h.initialControl prog w.pc w.ec

end IncrPP
end Incr
