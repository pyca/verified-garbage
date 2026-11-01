module

public import VerifiedGarbage.Proof.Bignum.X86.CrtABI
public import VerifiedGarbage.Proof.Weierstrass.PointContract
public import VerifiedGarbage.Impl.Bignum.X86.CrtLayout
public import VerifiedGarbage.Proof.Dsa.X86.StackArgument
import VerifiedGarbage.Proof.Dsa.X86.ABIResources
import VerifiedGarbage.Proof.Weierstrass.X86.CallOps
import VerifiedGarbage.Proof.Bignum.X86.CrtLayout
public import VerifiedGarbage.Proof.Mont.X86.OutsZ

/-! # Caller resources for the public RSA workspace -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86

theorem CrtABI.space {s : State} (A : CrtABI s) :
    VG.Impl.Bignum.X86.Crt.size (Spec.Rsa.modulusWords (arg s 3).toNat) ≤
      (arg s 17).toNat * 8 := by
  have H := Crt.shared_scratch A.lengths.1
  have := A.scratchLength
  omega

theorem CrtABI.used {s : State} (A : CrtABI s) : 224 ≤ (arg s 17).toNat * 8 := by
  have H := A.space
  rw [Crt.size_eq] at H
  omega

theorem CrtABI.stackArgument {s : State} (A : CrtABI s) {i : Nat} (hi : i < 18) :
    StackArgument s (argumentPointer s 16) ((arg s 17).toNat * 8) i := by
  apply stackArgument_of (count := 18) (by have := A.stackBound; omega) hi
  · rw [A.rd, A.wr]; simp
  · exact A.scratchArgs.symm

theorem CrtABI.stack {s : State} (A : CrtABI s) :
    StkOk (s.gpr .esp) (argumentPointer s 16) ((arg s 17).toNat * 8) := by
  apply VG.Proof.Weierstrass.X86.stkOk_of (by decide : 20 ≤ 96) A.stackLow
  · have H := A.scratchBound
    simpa only [argumentPointer, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans (arg s 16).isLt (by decide : 2 ^ 32 < 2 ^ 64))] using H
  · have H : 224 ≤ (arg s 17).toNat * 8 := A.used; omega
  · exact A.belowScratch

theorem CrtABI.room {s : State} (A : CrtABI s) :
    CallRoom (s.gpr .esp) (argumentPointer s 16) ((arg s 17).toNat * 8) := by
  refine ⟨A.stackLow, ?_⟩
  simp only [below]
  rw [VG.X86.Taint.sub_setWidth A.stackLow]
  exact A.belowScratch

end VG.Proof.Bignum.X86
