module

public import VerifiedGarbage.Proof.Bignum.X86.PrecomputeABI
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

theorem PrecomputeABI.space {s : State} (A : PrecomputeABI s) :
    VG.Impl.Bignum.X86.PublicContext.size (Spec.Rsa.modulusWords (arg s 3).toNat) ≤
      (arg s 5).toNat * 8 := by
  rw [PublicContext.size_contract]
  have := A.scratchLength
  omega

theorem PrecomputeABI.used {s : State} (A : PrecomputeABI s) : 384 ≤ (arg s 5).toNat * 8 := by
  have H := A.space
  rw [PublicContext.size_eq] at H
  omega

theorem PrecomputeABI.stackArgument {s : State} (A : PrecomputeABI s) {i : Nat} (hi : i < 6) :
    StackArgument s (argumentPointer s 4) ((arg s 5).toNat * 8) i := by
  apply stackArgument_of (count := 6) (by have := A.stackBound; omega) hi
  · rw [A.rd, A.wr]; simp
  · exact A.scratchArgs.symm

theorem PrecomputeABI.stack {s : State} (A : PrecomputeABI s) :
    StkOk (s.gpr .esp) (argumentPointer s 4) ((arg s 5).toNat * 8) := by
  apply VG.Proof.Weierstrass.X86.stkOk_of (by decide : 20 ≤ 96) A.stackLow
  · have H := A.scratchBound
    simpa only [argumentPointer, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans (arg s 4).isLt (by decide : 2 ^ 32 < 2 ^ 64))] using H
  · have H : 384 ≤ (arg s 5).toNat * 8 := A.used; omega
  · exact A.belowScratch


end VG.Proof.Bignum.X86
