import Incr.IncrPP.Semantics.Probe

/-!
# Raw derivation projections

These definitions inspect retained witnesses. No unvalidated event record
or sandbox execution adapter supplies their values.
-/

namespace Incr.IncrPP

noncomputable section

variable {sig : Signature} {m : CommandModel sig}

namespace LiveDerivation

/-- The consumed chunk, not the whole memo input. -/
def input : ∀ {before head after out},
    LiveDerivation m before head after out → Chunk
  | _, _, _, _, .pipelineOpen _ _ _ _ s' _ _ _ _ _ _ _ _ _ _ _ _ => ⟨s', .open⟩
  | _, _, _, _, .uncacheClose _ _ _ _ s _ _ _ _ _ _ _ _ _ _ _ => ⟨s, .eof⟩
  | _, _, _, _, .cacheCloseMiss _ _ _ _ s _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => ⟨s, .eof⟩
  | _, _, _, _, .cacheCloseHit _ _ _ _ s _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => ⟨s, .eof⟩
  | _, _, _, _, .uncacheStandalone _ _ s _ _ _ _ _ _ => ⟨s, .eof⟩
  | _, _, _, _, .cacheStandaloneMiss _ _ s _ _ _ _ _ _ _ _ _ => ⟨s, .eof⟩
  | _, _, _, _, .cacheStandaloneHit _ _ s _ _ _ _ _ _ _ => ⟨s, .eof⟩

/-- The executing result or whole memo result, not the applied replay patch. -/
def result : ∀ {before head after out},
    LiveDerivation m before head after out → Result sig
  | _, _, _, _, .pipelineOpen _ _ _ _ _ _ r _ _ _ _ _ _ _ _ _ _ => r
  | _, _, _, _, .uncacheClose _ _ _ _ _ r _ _ _ _ _ _ _ _ _ _ => r
  | _, _, _, _, .cacheCloseMiss _ _ _ _ _ r _ _ _ _ _ _ _ _ _ _ _ _ _ _ => r
  | _, _, _, _, .cacheCloseHit _ _ _ _ _ _ memo _ _ _ _ _ _ _ _ _ _ _ _ _ _ => memo.result
  | _, _, _, _, .uncacheStandalone _ _ _ r _ _ _ _ _ => r
  | _, _, _, _, .cacheStandaloneMiss _ _ _ r _ _ _ _ _ _ _ _ => r
  | _, _, _, _, .cacheStandaloneHit _ _ _ memo _ _ _ _ _ _ => memo.result

/-- The produced chunk. A pipeline hit produces only its suffix. -/
def produced : ∀ {before head after out},
    LiveDerivation m before head after out → Chunk
  | _, _, _, _, .pipelineOpen _ _ _ _ _ _ r _ _ _ _ _ _ _ _ _ _ => r.output
  | _, _, _, _, .uncacheClose _ _ _ _ _ r _ _ _ _ _ _ _ _ _ _ => r.output
  | _, _, _, _, .cacheCloseMiss _ _ _ _ _ r _ _ _ _ _ _ _ _ _ _ _ _ _ _ => r.output
  | _, _, _, _, .cacheCloseHit _ _ _ _ _ t _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => ⟨t, .eof⟩
  | _, _, _, _, .uncacheStandalone _ _ _ r _ _ _ _ _ => r.output
  | _, _, _, _, .cacheStandaloneMiss _ _ _ r _ _ _ _ _ _ _ _ => r.output
  | _, _, _, _, .cacheStandaloneHit _ _ _ memo _ _ _ _ _ _ => memo.output

/-- The patch actually applied to the current shared filesystem. -/
def appliedPatch : ∀ {before head after out},
    LiveDerivation m before head after out → Patch sig
  | _, _, _, _, .pipelineOpen _ _ _ _ _ _ r _ _ _ _ _ _ _ _ _ _ => r.patch
  | _, _, _, _, .uncacheClose _ _ _ _ _ r _ _ _ _ _ _ _ _ _ _ => r.patch
  | _, _, _, _, .cacheCloseMiss _ _ _ _ _ r _ _ _ _ _ _ _ _ _ _ _ _ _ _ => r.patch
  | _, _, _, _, .cacheCloseHit _ _ _ _ _ _ _ delta'' _ _ _ _ _ _ _ _ _ _ _ _ _ => delta''
  | _, _, _, _, .uncacheStandalone _ _ _ r _ _ _ _ _ => r.patch
  | _, _, _, _, .cacheStandaloneMiss _ _ _ r _ _ _ _ _ _ _ _ => r.patch
  | _, _, _, _, .cacheStandaloneHit _ _ _ _ delta'' _ _ _ _ _ => delta''

/-- The current filesystem for executing calls. Hits make no denotation call. -/
def callFS : ∀ {before head after out},
    LiveDerivation m before head after out → Option (FS sig)
  | _, _, _, _, .pipelineOpen w _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => some w.fs
  | _, _, _, _, .uncacheClose w _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => some w.fs
  | _, _, _, _, .cacheCloseMiss w _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => some w.fs
  | _, _, _, _, .cacheCloseHit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => none
  | _, _, _, _, .uncacheStandalone w _ _ _ _ _ _ _ _ => some w.fs
  | _, _, _, _, .cacheStandaloneMiss w _ _ _ _ _ _ _ _ _ _ _ => some w.fs
  | _, _, _, _, .cacheStandaloneHit _ _ _ _ _ _ _ _ _ _ => none

/-- The actual buffer map passed to put. Standalone rules do not route. -/
def routingBuffers : ∀ {before head after out},
    LiveDerivation m before head after out → Option (FMap Nat Chunk)
  | _, _, _, _, .pipelineOpen w _ i _ _ s'' _ buffer' _ _ _ _ _ _ _ _ _ => some (w.buffer[i ↦ ⟨s'', .open⟩])
  | _, _, _, _, .uncacheClose w _ i _ _ _ _ buffer' _ _ _ _ _ _ _ _ => some (w.buffer ∖ i)
  | _, _, _, _, .cacheCloseMiss w _ i _ _ _ _ buffer' _ _ _ _ _ _ _ _ _ _ _ _ => some (w.buffer ∖ i)
  | _, _, _, _, .cacheCloseHit w _ i _ _ _ _ _ buffer' _ _ _ _ _ _ _ _ _ _ _ _ => some (w.buffer ∖ i)
  | _, _, _, _, .uncacheStandalone _ _ _ _ _ _ _ _ _ => none
  | _, _, _, _, .cacheStandaloneMiss _ _ _ _ _ _ _ _ _ _ _ _ => none
  | _, _, _, _, .cacheStandaloneHit _ _ _ _ _ _ _ _ _ _ => none

end LiveDerivation

namespace VanillaDerivation

/-- The consumed chunk, not the whole memo input. -/
def input : ∀ {before head after out},
    VanillaDerivation m before head after out → Chunk
  | _, _, _, _, .openStep _ _ _ s' _ _ _ _ _ _ _ _ _ => ⟨s', .open⟩
  | _, _, _, _, .closeStep _ _ _ s _ _ _ _ _ _ _ _ _ => ⟨s, .eof⟩
  | _, _, _, _, .standalone _ _ s _ _ _ _ _ => ⟨s, .eof⟩

/-- The executing result or whole memo result, not the applied replay patch. -/
def result : ∀ {before head after out},
    VanillaDerivation m before head after out → Result sig
  | _, _, _, _, .openStep _ _ _ _ _ r _ _ _ _ _ _ _ => r
  | _, _, _, _, .closeStep _ _ _ _ r _ _ _ _ _ _ _ _ => r
  | _, _, _, _, .standalone _ _ _ r _ _ _ _ => r

/-- The produced chunk. A pipeline hit produces only its suffix. -/
def produced : ∀ {before head after out},
    VanillaDerivation m before head after out → Chunk
  | _, _, _, _, .openStep _ _ _ _ _ r _ _ _ _ _ _ _ => r.output
  | _, _, _, _, .closeStep _ _ _ _ r _ _ _ _ _ _ _ _ => r.output
  | _, _, _, _, .standalone _ _ _ r _ _ _ _ => r.output

/-- The patch actually applied to the current shared filesystem. -/
def appliedPatch : ∀ {before head after out},
    VanillaDerivation m before head after out → Patch sig
  | _, _, _, _, .openStep _ _ _ _ _ r _ _ _ _ _ _ _ => r.patch
  | _, _, _, _, .closeStep _ _ _ _ r _ _ _ _ _ _ _ _ => r.patch
  | _, _, _, _, .standalone _ _ _ r _ _ _ _ => r.patch

/-- The current filesystem for executing calls. Hits make no denotation call. -/
def callFS : ∀ {before head after out},
    VanillaDerivation m before head after out → Option (FS sig)
  | _, _, _, _, .openStep w _ _ _ _ _ _ _ _ _ _ _ _ => some w.fs
  | _, _, _, _, .closeStep w _ _ _ _ _ _ _ _ _ _ _ _ => some w.fs
  | _, _, _, _, .standalone w _ _ _ _ _ _ _ => some w.fs

/-- The actual buffer map passed to put. Standalone rules do not route. -/
def routingBuffers : ∀ {before head after out},
    VanillaDerivation m before head after out → Option (FMap Nat Chunk)
  | _, _, _, _, .openStep w _ i _ s'' _ buffer' _ _ _ _ _ _ => some (w.buffer[i ↦ ⟨s'', .open⟩])
  | _, _, _, _, .closeStep w _ i _ _ _ buffer' _ _ _ _ _ _ => some (w.buffer ∖ i)
  | _, _, _, _, .standalone _ _ _ _ _ _ _ _ => none

end VanillaDerivation

namespace ProbeDerivation

/-- The consumed chunk, not the whole memo input. -/
def input {executor : Executor} {before head after out}
    (d : ProbeDerivation m executor before head after out) : Chunk :=
  match executor with
  | .live => LiveDerivation.input d
  | .vanilla => VanillaDerivation.input d

/-- The executing result or whole memo result, not the applied replay patch. -/
def result {executor : Executor} {before head after out}
    (d : ProbeDerivation m executor before head after out) : Result sig :=
  match executor with
  | .live => LiveDerivation.result d
  | .vanilla => VanillaDerivation.result d

/-- The produced chunk. A pipeline hit produces only its suffix. -/
def produced {executor : Executor} {before head after out}
    (d : ProbeDerivation m executor before head after out) : Chunk :=
  match executor with
  | .live => LiveDerivation.produced d
  | .vanilla => VanillaDerivation.produced d

/-- The patch actually applied to the current shared filesystem. -/
def appliedPatch {executor : Executor} {before head after out}
    (d : ProbeDerivation m executor before head after out) : Patch sig :=
  match executor with
  | .live => LiveDerivation.appliedPatch d
  | .vanilla => VanillaDerivation.appliedPatch d

/-- The current filesystem for executing calls. Hits make no denotation call. -/
def callFS {executor : Executor} {before head after out}
    (d : ProbeDerivation m executor before head after out) : Option (FS sig) :=
  match executor with
  | .live => LiveDerivation.callFS d
  | .vanilla => VanillaDerivation.callFS d

/-- The actual buffer map passed to put. Standalone rules do not route. -/
def routingBuffers {executor : Executor} {before head after out}
    (d : ProbeDerivation m executor before head after out) : Option (FMap Nat Chunk) :=
  match executor with
  | .live => LiveDerivation.routingBuffers d
  | .vanilla => VanillaDerivation.routingBuffers d

end ProbeDerivation

end
end IncrPP
end Incr
