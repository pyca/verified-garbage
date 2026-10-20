module

public import Init.Prelude
public import VerifiedGarbage.Impl.Bignum.Arm.MontCallSquareReduceWith
public import VerifiedGarbage.Spec.Rsa.Mont
public import VerifiedGarbage.Proof.Bignum.Arm.MontCallWithLaw
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Bignum.Arm.SquareReduceWithOp
public import VerifiedGarbage.Proof.Bignum.Arm.RowKernel
import VerifiedGarbage.Proof.Bignum.Arm.MontCallSquareReduceWithArithmetic
import VerifiedGarbage.Proof.Bignum.Arm.MontCallSquareReduceWithCT
import VerifiedGarbage.Proof.Bignum.Arm.MontCallWithContract

/-! The new diagonal square satisfies the unchanged callable RSA ABI. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem montCallSquareReduceWith_law (K : RowKernel) :
    CallArithmeticLaw (MontCallSquareReduceWith.arithmetic K.code) where
  correct := montCallSquareReduceWithArithmetic_ok K
  ct := montCallSquareReduceWithArithmetic_ct K
  stack := by
    simp only [MontCallSquareReduceWith.arithmetic, MontCallWith.dispatch, FrameStack.armStack,
      squareBodyReduceWith_stack K]
    rfl

theorem montCallSquareReduceWith_verified (K : RowKernel) :
    Verified target (MontCallSquareReduceWith.code K.code) (Spec.Rsa.Mont.mulContract abi 40) :=
  montCallWith_verified _ (montCallSquareReduceWith_law K)

theorem montCallSquareReduceWith_stack (K : RowKernel) : FrameStack.armStack (MontCallSquareReduceWith.code K.code) ≤ 40 :=
  montCallWith_stack _ (montCallSquareReduceWith_law K)

end VG.Proof.Bignum.Arm
