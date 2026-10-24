module

import VerifiedGarbage.Proof.Rsa.PPC64LE.KcImplies
public import VerifiedGarbage.Impl.Rsa.PPC64LE.CheckKey
public import VerifiedGarbage.Impl.Rsa.PPC64LE.CheckCrtKey
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Rsa.PPC64LE.KcCkMain
import VerifiedGarbage.Proof.Rsa.PPC64LE.KcCckMain
import VerifiedGarbage.Proof.Rsa.PPC64LE.KcCkCT
import VerifiedGarbage.Proof.Rsa.PPC64LE.KcCckCT
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target

/-! # `vg_rsa_check_key` and `vg_rsa_check_crt_key` on PPC64LE: verified against the shared contracts -/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.KeyCheck

open VG VG.PPC64LE

/-- `vg_rsa_check_key`. -/
theorem ck_verified :
    Verified target VG.Impl.Rsa.PPC64LE.CheckKey.code (Spec.Rsa.checkKeyContract abi) :=
  Verified.of_correct ck_correct ck_ct ck_implies

/-- `vg_rsa_check_crt_key`. -/
theorem cck_verified :
    Verified target VG.Impl.Rsa.PPC64LE.CheckCrtKey.code (Spec.Rsa.checkCrtKeyContract abi) :=
  Verified.of_correct cck_correct cck_ct cck_implies

end VG.Proof.Rsa.PPC64LE.KeyCheck
