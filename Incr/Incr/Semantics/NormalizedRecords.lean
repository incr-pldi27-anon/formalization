import Incr.Incr.Semantics.Observations

/-!
# Normalized file occurrences for proof support

These lists describe file entries, not the `def:paper-timestamps` public whole-map
collection.
The scan is retained only to transport existing proofs by occurrence bridges.
-/

open Incr
namespace Incr.Incr

noncomputable section

variable {sig : Signature}

/-- Proof-support occurrences from an enumeration of patch-entry updates. -/
def applicationRecords (fs : FS sig) (patch : Patch sig) : Records sig :=
  (patch.entries.toList.scanl (fun acc kv =>
    match kv.2 with
    | .write f => acc[kv.1 ↦ f]
    | .delete => acc ∖ kv.1) fs).flatMap fsRecords

/-- Normalized world occurrences include sandbox views and cached patches. -/
def worldRecords (w : World sig) : Records sig :=
  fsRecords w.fs ++ cacheRecords w.cache ++
    w.sandbox.entries.toList.flatMap fun kv =>
      fsRecords kv.2.base ++ patchRecords kv.2.patch ++
        applicationRecords kv.2.base kv.2.patch

/-- The patch actually applied to the live filesystem. An open sandbox step
stages its result and applies no live patch. A close applies the combined
patch, while a hit applies the whole memo patch. -/
def IncrDerivation.livePatch {m : CommandModel sig} :
    ∀ {w head w' out}, IncrDerivation m w head w' out → Option (Patch sig)
  | _, _, _, _, .pipelineOpen _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => none
  | _, _, _, _, .uncacheClose _ _ _ sb _ r _ _ _ _ _ _ _ _ _ _ => some (sb.patch ⊎ r.patch)
  | _, _, _, _, .cacheCloseMiss _ _ _ sb _ r _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      some (sb.patch ⊎ r.patch)
  | _, _, _, _, .cacheCloseHit _ _ _ _ _ _ memo _ _ _ _ _ _ _ _ _ _ _ => some memo.patch
  | _, _, _, _, .uncacheStandalone _ _ _ r _ _ _ _ _ => some r.patch
  | _, _, _, _, .cacheStandaloneMiss _ _ _ r _ _ _ _ _ _ _ => some r.patch
  | _, _, _, _, .cacheStandaloneHit _ _ _ memo _ _ _ _ _ => some memo.patch

/-- The live application selected by this recorded rule. -/
def StepDerivation.livePatch {m : CommandModel sig} {h : Host sig}
    {executor : Executor} {prog : sig.Prog} (d : StepDerivation m h executor prog) :
    Option (Patch sig) := by
  cases executor with
  | incr => exact IncrDerivation.livePatch d.probe
  | vanilla => exact some (VanillaDerivation.result d.probe).patch

/-- Normalized step occurrences, retained only to support proof transport. -/
def StepDerivation.records {m : CommandModel sig} {h : Host sig}
    {executor : Executor} {prog : sig.Prog} (d : StepDerivation m h executor prog) : Records sig :=
  worldRecords d.before ++ worldRecords d.selected ++ worldRecords d.after ++
    patchRecords (ProbeDerivation.result d.probe).patch ++
    (match ProbeDerivation.callFS d.probe with
    | none => []
    | some fs => fsRecords fs) ++
    (match d.livePatch with
    | none => []
    | some patch => patchRecords patch ++ applicationRecords d.selected.fs patch)

/-- Normalized prefix occurrences include the initial world. -/
def Prefix.records {m : CommandModel sig} {h : Host sig} {executor : Executor}
    {prog : sig.Prog} {start : World sig} (pre : Prefix m h executor prog start) : Records sig :=
  worldRecords start ++ pre.trace.flatMap StepDerivation.records

end
end Incr.Incr
