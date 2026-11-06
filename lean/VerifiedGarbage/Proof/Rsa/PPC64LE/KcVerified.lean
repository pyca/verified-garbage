module

import VerifiedGarbage.Proof.Rsa.PPC64LE.KcImplies
public import VerifiedGarbage.Impl.Rsa.PPC64LE.CheckKey
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Rsa.PPC64LE.KcCkMain
import VerifiedGarbage.Proof.Rsa.PPC64LE.KcCkCT
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Rsa.Contract
public import VerifiedGarbage.Impl.Rsa.PPC64LE.KeyCheck
import VerifiedGarbage.Impl.Rsa.PPC64LE.KeyCheck
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubE
import VerifiedGarbage.Proof.Rsa.PPC64LE.KcBase
import VerifiedGarbage.Proof.Rsa.PPC64LE.KcCk
import VerifiedGarbage.Proof.Rsa.PPC64LE.KcCkPre
import VerifiedGarbage.Proof.Rsa.PPC64LE.KcFrame
import VerifiedGarbage.Spec.Rsa
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Rsa.PPC64LE.KcEntry

/-! # `vg_rsa_check_key` and `vg_rsa_check_crt_key` on PPC64LE: verified against the shared contracts -/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.KeyCheck

open VG VG.PPC64LE

/-- `vg_rsa_check_key`. -/
theorem ck_verified :
    Verified target VG.Impl.Rsa.PPC64LE.CheckKey.code (Spec.Rsa.checkKeyContract abi) :=
  Verified.of_correct ck_correct ck_ct ck_implies

end VG.Proof.Rsa.PPC64LE.KeyCheck
