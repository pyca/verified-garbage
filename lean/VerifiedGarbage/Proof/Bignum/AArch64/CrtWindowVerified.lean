module
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowDispatch
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBody

import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowCode
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowCodeCT
import VerifiedGarbage.Proof.Bignum.AArch64.CrtImplies
public import VerifiedGarbage.Proof.Rsa.Contract

/-! Wider-window RSA CRT against the unchanged shared contract. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64

theorem verified (W : Window) (M : Mont) (S : Selector) :
    Verified AArch64.target (VG.Impl.Rsa.AArch64.WindowFive.code W.code S.code M.mm)
      (Proof.Rsa.privateCrtContract abi 0) :=
  Verified.of_correct (crtCode_correct W M S) (crtCode_constantTime_of W M S) crt_implies

end VG.Proof.Bignum.AArch64.WindowFive
