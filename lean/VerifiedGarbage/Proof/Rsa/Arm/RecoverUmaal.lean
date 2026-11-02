module
public import VerifiedGarbage.Proof.Rsa.Arm.InvLaw

import VerifiedGarbage.Proof.Rsa.Arm.RvVerified
import VerifiedGarbage.Proof.Bignum.Arm.UmaalArithmetic
public import Init.Prelude
public import VerifiedGarbage.Impl.Bignum.Arm.UmaalArithmetic
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Impl.Rsa.Arm.Recover
public import VerifiedGarbage.Spec.Rsa.Contract

/-! Prime recovery reuses the exact row transformation of the RSA private operation. -/

@[expose] public section
namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Impl.Bignum.Arm

theorem recover_primes_umaal_verified [VG.Proof.Rsa.Arm.Keys.InvLaw] :
    Verified target (umaalArithmetic Impl.Rsa.Arm.Recover.code)
      (Spec.Rsa.recoverPrimesContract abi 56) :=
  Proof.Bignum.Arm.umaalArithmetic_verified recover_primes_verified

end VG.Proof.Rsa.Arm.Recover
