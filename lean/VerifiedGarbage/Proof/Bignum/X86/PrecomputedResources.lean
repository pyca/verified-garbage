module

public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedABI
public import VerifiedGarbage.Proof.Weierstrass.PointContract
public import VerifiedGarbage.Impl.Bignum.X86.PublicContext
public import VerifiedGarbage.Proof.Dsa.X86.StackArgument
import VerifiedGarbage.Proof.Dsa.X86.ABIResources
import VerifiedGarbage.Proof.Weierstrass.X86.CallOps
import VerifiedGarbage.Proof.Bignum.X86.PublicLayout

/-! # Caller resources for the public RSA workspace -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86

theorem PrecomputedABI.space {s : State} (A : PrecomputedABI s) :
    VG.Impl.Bignum.X86.PublicContext.size (Spec.Rsa.modulusWords (arg s 1).toNat) ≤
      (arg s 9).toNat * 8 := by
  rw [PublicContext.size_contract]
  have := A.scratchLength
  omega

theorem PrecomputedABI.used {s : State} (A : PrecomputedABI s) : 384 ≤ (arg s 9).toNat * 8 := by
  have H := A.space
  rw [PublicContext.size_eq] at H
  omega

theorem PrecomputedABI.stackArgument {s : State} (A : PrecomputedABI s) {i : Nat} (hi : i < 10) :
    StackArgument s (argumentPointer s 8) ((arg s 9).toNat * 8) i := by
  apply stackArgument_of (count := 10) (by have := A.stackBound; omega) hi
  · rw [A.rd, A.wr]; simp
  · exact A.scratchArgs.symm

theorem PrecomputedABI.stack {s : State} (A : PrecomputedABI s) :
    StkOk (s.gpr .esp) (argumentPointer s 8) ((arg s 9).toNat * 8) := by
  apply VG.Proof.Weierstrass.X86.stkOk_of (Nat.le_refl 20) A.stackLow
  · have H := A.scratchBound
    simpa only [argumentPointer, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans (arg s 8).isLt (by decide : 2 ^ 32 < 2 ^ 64))] using H
  · have H : 384 ≤ (arg s 9).toNat * 8 := A.used; omega
  · exact A.belowScratch


end VG.Proof.Bignum.X86
