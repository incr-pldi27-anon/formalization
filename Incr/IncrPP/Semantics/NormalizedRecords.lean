import Incr.IncrPP.Semantics.Observations

/-!
# Normalized Live file occurrences

These lists support timestamp proofs. They are not E.3 whole-map records.
Implementation scans preserve file support, not the paper's map inventory.
-/

namespace Incr.IncrPP

noncomputable section

variable {sig : Signature}

/-- Proof support for one arbitrary patch-entry enumeration. -/
def applicationRecords (fs : FS sig) (patch : Patch sig) : Records sig :=
  (patch.entries.toList.scanl (fun acc kv =>
    match kv.2 with
    | .write file => acc[kv.1 ↦ file]
    | .delete => acc ∖ kv.1) fs).flatMap fsRecords

/-- Normalized live, cache, snapshot, and accumulated-patch file occurrences. -/
def worldRecords (world : World sig) : Records sig :=
  fsRecords world.fs ++ cacheRecords world.cache ++
    world.sandbox.entries.toList.flatMap fun kv =>
      fsRecords kv.2.base ++ patchRecords kv.2.patch

/-- File occurrences of a step, including redundant scan support. -/
def StepDerivation.records {m : CommandModel sig} {h : Host sig}
    {executor : Executor} {prog : sig.Prog} (d : StepDerivation m h executor prog) : Records sig :=
  worldRecords d.before ++ worldRecords d.selected ++ worldRecords d.after ++
    patchRecords (ProbeDerivation.result d.probe).patch ++
    (match ProbeDerivation.callFS d.probe with
    | none => []
    | some fs => fsRecords fs) ++
    patchRecords (ProbeDerivation.appliedPatch d.probe) ++
    applicationRecords d.selected.fs (ProbeDerivation.appliedPatch d.probe)

/-- Normalized initial-world and trace occurrences. -/
def Prefix.records {m : CommandModel sig} {h : Host sig} {executor : Executor}
    {prog : sig.Prog} {start : World sig} (pre : Prefix m h executor prog start) : Records sig :=
  worldRecords start ++ pre.trace.flatMap StepDerivation.records

end
end IncrPP
end Incr
