module

public import VerifiedGarbage.Impl.Modes.Ops

/-!
# CBC that updates the chaining value, one block at a time, for any target

`Mode.cbcEncChained` and `Mode.cbcDecChained`: CBC encryption and
decryption (`Mode.cbcEnc`, `Mode.cbcDec`), whose chaining value goes back to
the IV at the end (`ivOut`): after the last block it is `Cₙ`, the last
ciphertext block, and with no blocks the IV.
-/

@[expose] public section

namespace VG.Impl.Modes.Mode

variable (bw : Nat)

/-- CBC encryption, the last ciphertext block back to the IV. -/
def cbcEncChained : Mode := { cbcEnc bw with ivOut := true }

/-- CBC decryption, the last ciphertext block back to the IV. -/
def cbcDecChained : Mode := { cbcDec bw with ivOut := true }

end VG.Impl.Modes.Mode
