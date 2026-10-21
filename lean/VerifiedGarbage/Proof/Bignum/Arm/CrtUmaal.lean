module
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Impl.Bignum.Arm.CrtFn
public import VerifiedGarbage.Impl.Bignum.Arm.CrtFios
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Impl.Bignum.Arm.UmaalArithmetic
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Bignum.Arm.CrtVerified
import VerifiedGarbage.Proof.Bignum.Arm.UmaalArithmetic
import VerifiedGarbage.Proof.Bignum.Arm.InlineWindow
import VerifiedGarbage.Proof.Bignum.Arm.FiosRound
import VerifiedGarbage.Proof.Bignum.Arm.FiosCT

/-! # `vg_rsa_private_crt_umaal`: the private-key operation with `umaal` rows -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG.Arm VG.Impl.Bignum.Arm

theorem crtUmaal_verified :
    Verified target CrtFios.code (Spec.Rsa.privateCrtContract abi 56) :=
  umaalArithmetic_verified (crt_verified (kernel := InlineWindow.kernel Fios.round Fios.round_law (by
    intro base size tmp a b mod acc n i _ hi
    exact Fios.round_ct hi)))

end VG.Proof.Bignum.Arm
