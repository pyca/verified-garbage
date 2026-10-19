module

public import VerifiedGarbage.Impl.Bignum.X86.CrtFn
public import VerifiedGarbage.Proof.Bignum.X86.CrtTransferTiming

/-! # The complete CRT arithmetic trace is independent of private components -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.Crt VG.Proof.Dsa.X86
open VG.Proof.Mont.X86.Dynamic

theorem copyPadded_relCT (n src dst : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (copyPadded n src dst)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  apply erased_relCT (copyPadded n src dst) (copyPadded 1 0 0)
    (VG.Taint.hintOf taint (workspaceTaint false) (copyPadded 1 0 0)) rfl rfl rfl
  rfl

theorem loadPower_relCT (n prime exponent : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (loadPower n prime exponent)
      (VG.X86.Taint.Agree (workspaceTaint false)) :=
  VG.RelCT.seq (copyArray_relCT _ _ _) (VG.RelCT.seq (copyArray_relCT _ _ _) (copyArray_relCT _ _ _))

theorem factorPower_relCT (n prime exponent output : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (factorPower n prime exponent output)
      (VG.X86.Taint.Agree (workspaceTaint false)) :=
  VG.RelCT.seq (loadPower_relCT _ _ _)
    (VG.RelCT.seq (checkedPrimePower_relCT n) (copyPadded_relCT _ _ _))

theorem loadCoefficient_relCT (n : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (loadCoefficient n)
      (VG.X86.Taint.Agree (workspaceTaint false)) :=
  VG.RelCT.seq (copyArray_relCT _ _ _) (VG.RelCT.seq (copyArray_relCT _ _ _)
    (VG.RelCT.seq (copyArray_relCT _ _ _) (copyArray_relCT _ _ _)))

theorem coefficient_relCT (n : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (coefficient n)
      (VG.X86.Taint.Agree (workspaceTaint false)) :=
  VG.RelCT.seq (loadCoefficient_relCT n)
    (VG.RelCT.seq (VG.RelCT.seq (primeMask_relCT n) (preparePrime_relCT n)) (crtCoefficient_relCT n))

theorem maskOutput_relCT (n : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (maskOutput n)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  apply erased_relCT (maskOutput n) (maskOutput 1)
    (VG.Taint.hintOf taint (workspaceTaint false) (maskOutput 1)) rfl rfl rfl
  rfl

end VG.Proof.Bignum.X86.Crt
