module

public import VerifiedGarbage.Proof.Rsa.Arm.Stage.Base
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.Arm.ByteWords

/-! # The ARMv7 key stages: Montgomery multiplication's working space

Its base is `M0`, `256` bytes before the key array `mBase`, so that its array
`j` is the key array `mBase + j` (its stride, `8 (w6 + 2)`, is that of the key
working space with `w = 2 w6 + 2`), and its header lies in the key arrays
16–19. `MR P s`: it is ready for a multiplication but for `r0`
(`ArithmeticReady`, `MR.ready`); steps that write neither the key arrays
16–20 nor frame word 0 keep it (`MR.of_keep`). A number of the key working
space below `2^(64 w6)` is Montgomery multiplication's number of the same
array (`numAt_eq`).
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt numAt wOf wordAt Layout Keeps)

/-! ## The arrays -/

theorem M0_addr {P : RP} (sz : Sizes P) (hf : P.B.toNat + P.Z ≤ 2 ^ 32) :
    State.addr P.M0 = off (State.addr P.B) P.oM :=
  addr_add (by
    have := sz.hdrM; have := sz.endM; have := sz.fits; have := arr_mono (w := P.w) (show mBase + 8 ≤ nArr by decide)
    have : 0 < P.lenM := by simp only [RP.lenM]; omega
    omega)

end VG.Proof.Rsa.Arm.Recover
