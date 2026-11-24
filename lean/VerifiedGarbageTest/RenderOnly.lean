module

public import VerifiedGarbage.TCB.Registration

/-!
# A target for the tests of the emitter

A test of the emitter renders the artifact of a small function, which it
proves `Verified` on its target. An `Artifact`'s proof is `VerifiedScrubbed`:
also that the code returns without secret residue, as its target defines it
(`Target.noResidue`). A test of how code is printed proves that of no code:
it makes its artifact on `renderOnly T`, the target `T` with a `noResidue`
that every code meets. Only tests use it: an artifact of the library is one
of a target of `TCB/`.
-/

@[expose] public section

namespace VG.Test

/-- The target `T` with a `noResidue` that every code meets: for a test of
the emitter, never for an artifact of the library. -/
abbrev renderOnly (T : Target) : Target := { T with noResidue := some fun _ _ _ => True }

/-- `Verified` on `T` is `VerifiedScrubbed` on `renderOnly T`, on a target whose
calling convention has no rule for any result (`Abi.retExt`), so that `RetAbi` holds of any
code. -/
theorem renderOnly_verified {T : Target} {c : Prog T.isa} {k : Contract T.isa} {retBits : Nat}
    (h : Verified T c k) (hr : ∀ ty, T.abi.retExt ty = none := by intro ty; cases ty <;> rfl) :
    VerifiedScrubbed (renderOnly T) c k retBits :=
  ⟨h, trivial, fun ty _ hf => by rw [show (renderOnly T).abi = T.abi from rfl, hr ty] at hf; cases hf⟩

end VG.Test
