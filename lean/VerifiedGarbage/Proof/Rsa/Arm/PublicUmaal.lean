module

public import VerifiedGarbage.Proof.Framework.Arm.CallF

public import VerifiedGarbage.Impl.Bignum.Arm.UmaalArithmetic
public import VerifiedGarbage.Impl.Bignum.Arm.PdFn
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Impl.Bignum.Arm.PcFn
public import Init.Prelude
import VerifiedGarbage.Proof.Bignum.Arm.PcVerified
import VerifiedGarbage.Proof.Bignum.Arm.PdVerified
import VerifiedGarbage.Proof.Bignum.Arm.UmaalArithmetic

/-! Public setup and exponentiation reuse the same exact UMAAL arithmetic transformation. -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem precompute_umaal_verified :
    Verified target (umaalArithmetic PcFn.code) (Spec.Rsa.publicPrecomputeContract abi 56) :=
  Proof.Bignum.Arm.umaalArithmetic_verified Proof.Bignum.Arm.precompute_verified

theorem public_precomputed_umaal_verified :
    Verified target (umaalArithmetic PdFn.code) (Spec.Rsa.publicPrecomputedCheckedContract abi 56) :=
  Proof.Bignum.Arm.umaalArithmetic_verified Proof.Bignum.Arm.pd_verified

theorem precompute_umaal_stack : FrameStack.armStack (umaalArithmetic PcFn.code) ≤ 56 := by
  decide +kernel

theorem public_precomputed_umaal_stack : FrameStack.armStack (umaalArithmetic PdFn.code) ≤ 56 := by
  decide +kernel

end VG.Proof.Rsa.Arm
