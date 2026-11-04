import Incr.Incr.Semantics.Common

/-!
# The host interface for recorded executions

Selection and completion remain abstract, as in `sec:model-host`.
This interface does not refer to the current formalization's traces.
The host requirements are stated later, over the new execution prefixes.
-/

open Incr
namespace Incr.Incr

variable {sig : Signature}

/-- The assignment and external input at one pipeline entry. -/
structure PipelineInit (sig : Signature) where
  probes : List sig.Probe
  input : Chunk

/-- The selected probe and the host input supplied at this selection. -/
structure Selection (sig : Signature) where
  head : Head sig
  init : Option (PipelineInit sig)
  delivery : Option Chunk

/-- The paper's abstract initial control, selection, and completion judgments. -/
structure Host (sig : Signature) where
  initialControl : sig.Prog → sig.PC → Nat → Prop
  select : sig.Prog → World sig → Selection sig → World sig → Prop
  complete : sig.Prog → World sig → Prop

/-- Initial worlds have no pipeline and no pending standalone input. -/
def Initial (h : Host sig) (prog : sig.Prog) (w : World sig) : Prop :=
  w.buffer = ∅ ∧ w.sandbox = ∅ ∧ w.stdin = .emptyEOF ∧
    h.initialControl prog w.pc w.ec

end Incr.Incr
