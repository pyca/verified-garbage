module
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowDispatch
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBody

import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowCode
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowCodeCT
import VerifiedGarbage.Proof.Bignum.AArch64.CrtImplies
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetup
public import VerifiedGarbage.Proof.Rsa.Contract
public import VerifiedGarbage.Proof.Rsa.AArch64.PrivCallees

/-! Wider-window RSA CRT against the unchanged shared contract, and
`vg_rsa_private_crt_precomputed`, its code without the check `p q = n`,
against `privateCrtProductContract`, for keys that have it. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64

theorem verified (W : Window) (M : Mont) (S : Selector) :
    Verified AArch64.target (VG.Impl.Rsa.AArch64.WindowFive.code W.code S.code M.mm)
      (Proof.Rsa.privateCrtContract abi 0) :=
  Verified.of_correct (crtCode_correct W M S) (crtCode_constantTime_of W M S) crt_implies

theorem verifiedGiven (W : Window) (M : Mont) (S : Selector) :
    Verified AArch64.target (VG.Impl.Rsa.AArch64.WindowFive.codeGiven W.code S.code M.mm)
      Proof.Rsa.AArch64.privateCrtProductContract :=
  Verified.of_correct (k := Proof.Rsa.AArch64.crtPA)
    (fun s (h : Proof.Rsa.AArch64.crtPA.pre s) => crtCodeWith_correct W M S checksGiven_okG s h.1 h.2)
    (crtCodeWith_constantTime W M S checksGiven_ct checksGiven_okG) crtP_implies

end VG.Proof.Bignum.AArch64.WindowFive
