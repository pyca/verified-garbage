module

public import VerifiedGarbage.Impl.Bignum.X86.CopyArray
public import VerifiedGarbage.Impl.Bignum.X86.CheckedPrimePower
public import VerifiedGarbage.Impl.Bignum.X86.CrtRecombine
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
import VerifiedGarbage.Proof.Bignum.X86.CrtArithmeticTiming
import VerifiedGarbage.Proof.Bignum.X86.PrimePowerTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Fixed traces for private RSA transfers, powers and recombination -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Dsa.X86 VG.Proof.Mont.X86.Dynamic

theorem copyArray_relCT (n src dst : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (copyArray n src dst)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  apply erased_relCT (copyArray n src dst) (copyArray 1 0 0)
    (VG.Taint.hintOf taint (workspaceTaint false) (copyArray 1 0 0)) rfl rfl rfl
  rfl

theorem checkedPrimePower_relCT (n : Nat) (hn : 0 < n) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (checkedPrimePower n)
      (VG.X86.Taint.Agree (workspaceTaint false)) :=
  VG.RelCT.seq (primeMask_relCT n) (primePower_relCT n hn)

theorem crtRecombine_relCT (n product q h residue out mult : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (crtRecombine n product q h residue out mult)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  apply erased_relCT (crtRecombine n product q h residue out mult) (crtRecombine 1 0 0 0 0 0 0)
    (VG.Taint.hintOf taint (workspaceTaint false) (crtRecombine 1 0 0 0 0 0 0)) rfl rfl rfl
  rfl

end VG.Proof.Bignum.X86
