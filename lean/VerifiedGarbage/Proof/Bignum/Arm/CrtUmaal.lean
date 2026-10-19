module
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Impl.Bignum.Arm.CrtFn
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Impl.Bignum.Arm.RowUmaal
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.TCB.Arm.Target

import VerifiedGarbage.Proof.Bignum.Arm.CrtVerified
import VerifiedGarbage.Proof.Bignum.Arm.RowUmaal

/-! # `vg_rsa_private_crt_umaal`: the private-key operation with `umaal` rows -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG.Arm VG.Impl.Bignum.Arm

theorem crtUmaal_verified :
    Verified target (umaalRows CrtFn.code) (Spec.Rsa.privateCrtContract abi 56) :=
  umaalRows_verified crt_verified

end VG.Proof.Bignum.Arm
