import Incr.Incr.Semantics.Rules

/-!
# Common recorded probe interface

The two Incr 1.0 executors share the same judgment indices. The dispatch below
selects a derivation family, not a new set of transition rules.
Every accessor reads a recorded derivation. There is no adapter to the
current formalization and no separate action record.
-/

open Incr
namespace Incr.Incr

variable {sig : Signature}

/-- The recorded probe derivation for the chosen executor. -/
def ProbeDerivation (m : CommandModel sig) :
    Executor → World sig → Head sig → World sig → Option Chunk → Type
  | .incr => IncrDerivation m
  | .vanilla => VanillaDerivation m

/-- The probe-rule skeleton for either executor. Shared execution conditions
belong to `Operational`; result typing is the ambient `DenotationShape` convention. -/
def ProbeStep (m : CommandModel sig) (executor : Executor)
    (w : World sig) (head : Head sig) (w' : World sig) (out : Option Chunk) : Prop :=
  Nonempty (ProbeDerivation m executor w head w' out)

namespace ProbeDerivation

variable {m : CommandModel sig} {executor : Executor} {w : World sig}
  {head : Head sig} {w' : World sig} {out : Option Chunk}

/-- Consumed input, including only the unread input on a pipeline hit. -/
def input (d : ProbeDerivation m executor w head w' out) : Chunk := by
  cases executor with
  | incr => exact d.input
  | vanilla => exact d.input

/-- The denotation result or the whole memo result on a hit. -/
def result (d : ProbeDerivation m executor w head w' out) : Result sig := by
  cases executor with
  | incr => exact d.result
  | vanilla => exact d.result

/-- Output produced at this step, before routing. A hit produces its suffix. -/
def produced (d : ProbeDerivation m executor w head w' out) : Chunk := by
  cases executor with
  | incr => exact d.produced
  | vanilla => exact d.result.output

/-- The exact buffer map passed to `put` by this derivation.
Open rules replace the source with its unread remainder. Closing rules remove it.
Standalone rules do not route through pipeline buffers. -/
def routingBuffers (d : ProbeDerivation m executor w head w' out) :
    Option (FMap Nat Chunk) := by
  cases executor with
  | incr =>
    cases d with
    | pipelineOpen p i sb s' s'' => exact some (w.buffer[i ↦ ⟨s'', .open⟩])
    | uncacheClose p i => exact some (w.buffer ∖ i)
    | cacheCloseMiss p i => exact some (w.buffer ∖ i)
    | cacheCloseHit p i => exact some (w.buffer ∖ i)
    | uncacheStandalone => exact none
    | cacheStandaloneMiss => exact none
    | cacheStandaloneHit => exact none
  | vanilla =>
    cases d with
    | openStep p i s' s'' => exact some (w.buffer[i ↦ ⟨s'', .open⟩])
    | closeStep p i => exact some (w.buffer ∖ i)
    | standalone => exact none

/-- The concrete routing input reproduces the actual pipeline rule's result.
This accessor fact uses only retained rule premises, not numbered lemmas. -/
theorem routingBuffers_pipeline (d : ProbeDerivation m executor w head w' out)
    (p : sig.Probe) (i : Nat) (hp : head = .pipeline p i) :
    ∃ buffers, routingBuffers d = some buffers ∧
      put buffers i (produced d) = some (w'.buffer, out) := by
  cases hp
  cases executor <;> cases d <;>
    simp_all only [routingBuffers, produced, result, IncrDerivation.produced,
      VanillaDerivation.result, closeWorld, updateWorld, Option.some.injEq,
      exists_eq_left'] <;> assumption

/-- The call filesystem, or `none` when the rule replays without a call. -/
def callFS (d : ProbeDerivation m executor w head w' out) : Option (FS sig) := by
  cases executor with
  | incr => exact d.callFS
  | vanilla => exact d.callFS

/-- Local freshness for this chosen call. Replays make no fresh call. -/
def Fresh (d : ProbeDerivation m executor w head w' out) : Prop :=
  match callFS d with
  | none => True
  | some fs => FreshPatch (result d).patch fs w.fs

end ProbeDerivation

end Incr.Incr
