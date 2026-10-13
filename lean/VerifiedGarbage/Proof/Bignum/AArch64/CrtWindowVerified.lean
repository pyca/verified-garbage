module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowCode
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowCodeCT
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtImplies
import Mathlib.Data.Int.ModEq
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTN

/-! Wider-window RSA CRT against the unchanged shared contract. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64

theorem verified (W : Window) (M : Mont) (S : Selector) :
    Verified AArch64.target (VG.Impl.Rsa.AArch64.WindowFive.code W.code S.code M.mm)
      (Spec.Rsa.privateCrtContract abi 0) :=
  Verified.of_correct (crtCode_correct W M S) (crtCode_constantTime_of W M S) crt_implies

end VG.Proof.Bignum.AArch64.WindowFive
