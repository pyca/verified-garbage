module

public import VerifiedGarbage.Impl.Bignum.X86.CrtCoefficient
public import VerifiedGarbage.Impl.Bignum.X86.CheckFactorProduct
public import VerifiedGarbage.Impl.Bignum.X86.PrimeMask
public import VerifiedGarbage.Proof.Bignum.X86.WideProductTiming
public import VerifiedGarbage.Proof.Dsa.X86.ChecksTiming

/-! # CRT validation and coefficient arithmetic have secret-independent traces -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Dsa.X86
open VG.Impl.Mont.X86.Dynamic VG.Proof.Mont.X86.Dynamic

theorem reduceOperand_relCT (n operand : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (reduceOperand n operand)
      (VG.X86.Taint.Agree (workspaceTaint false)) :=
  VG.RelCT.seq (checkedProgramChange (mul_check false _ _ _ _ _ _) (by rfl))
    (checkedProgramChange (mul_check false _ _ _ _ _ _) (by rfl))

theorem subW_relCT (M : VG.Impl.Mont.Mod) (acc o a b : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (subW M acc o a b)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  apply erased_relCT (subW M acc o a b) (subW eraseMod 0 0 0 0)
    (VG.Taint.hintOf taint (workspaceTaint false) (subW eraseMod 0 0 0 0)) rfl rfl rfl
  rfl

theorem crtCoefficient_relCT (n : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (crtCoefficient n)
      (VG.X86.Taint.Agree (workspaceTaint false)) :=
  VG.RelCT.seq (reduceOperand_relCT n 5)
    (VG.RelCT.seq (subW_relCT _ _ _ _ _)
      (VG.RelCT.seq (checkedProgramChange (mul_check false _ _ _ _ _ _) (by rfl))
        (checkedProgramChange (mul_check false _ _ _ _ _ _) (by rfl))))

theorem checkFactorProduct_relCT (n product p q modulus mult : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (checkFactorProduct n product p q modulus mult)
      (VG.X86.Taint.Agree (workspaceTaint false)) :=
  VG.RelCT.seq (wideProduct_relCT _ _ _ _ _) (equal_relCT false _ _ _)

theorem primeMask_relCT (n : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (primeMask n)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  apply erased_relCT (primeMask n) (primeMask 1)
    (VG.Taint.hintOf taint (workspaceTaint false) (primeMask 1)) rfl rfl rfl
  rfl

end VG.Proof.Bignum.X86
