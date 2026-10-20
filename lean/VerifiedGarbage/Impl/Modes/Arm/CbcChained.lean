module

public import VerifiedGarbage.Impl.Modes.Arm.Seq

/-!
# CBC on ARMv7 that updates the chaining value, one block at a time

`cbcEncChained` and `cbcDecChained`: CBC encryption and decryption
(`cbcEnc`, `cbcDec`), which also return the chaining block in the IV
(`finish`): after the last block it is `Cₙ`, the last ciphertext block, and
with no blocks the IV.
-/

@[expose] public section

namespace VG.Impl.Modes.Arm

/-- CBC encryption, the last ciphertext block back to the IV. -/
def cbcEncChained : Mode := { cbcEnc with finish := true }

/-- CBC decryption, the last ciphertext block back to the IV. -/
def cbcDecChained : Mode := { cbcDec with finish := true }

end VG.Impl.Modes.Arm
