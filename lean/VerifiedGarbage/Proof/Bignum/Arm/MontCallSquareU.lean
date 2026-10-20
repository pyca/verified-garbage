module

public import Init.Prelude
public import VerifiedGarbage.Impl.Bignum.Arm.MontCallSquareU
public import VerifiedGarbage.Spec.Rsa.Mont
public import VerifiedGarbage.Proof.Bignum.Arm.MontCallWithLaw
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Bignum.Arm.MontCallSquareUArithmetic
import VerifiedGarbage.Proof.Bignum.Arm.MontCallSquareUCT
import VerifiedGarbage.Proof.Bignum.Arm.MontCallWithContract

/-! The new diagonal square satisfies the unchanged callable RSA ABI. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem montCallSquareU_law : CallArithmeticLaw MontCallSquareU.arithmetic where
  correct := montCallSquareUArithmetic_ok
  ct := montCallSquareUArithmetic_ct
  stack := rfl

theorem montCallSquareU_verified :
    Verified target MontCallSquareU.code (Spec.Rsa.Mont.mulContract abi 40) :=
  montCallWith_verified _ montCallSquareU_law

theorem montCallSquareU_stack : FrameStack.armStack MontCallSquareU.code ≤ 40 :=
  montCallWith_stack _ montCallSquareU_law

end VG.Proof.Bignum.Arm
