import Incr.Incr
import Incr.IncrPP

/-!
# Incr and Incr++

This root imports both formalizations. Shared definitions live under
`Incr.Model`, `Incr.Foundation`, and `Incr.Assumptions`. The original and
Incr++ protocols are peer modules. Each `thm_sound` carries an inline
`#guard_msgs` axiom check.
-/
