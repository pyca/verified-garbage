module
public import VerifiedGarbage.Proof.Dsa.X86.CheckingABI
import VerifiedGarbage.Proof.Weierstrass.X86.CallOps
public import VerifiedGarbage.Proof.Dsa.X86.StackArgument
public import VerifiedGarbage.Proof.Dsa.X86.StackFrame
import VerifiedGarbage.Proof.Dsa.X86.ABIResources

/-! # Stack and workspace resources of domain checking -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem CheckingABI.used {s : State} (A : CheckingABI s) : usedBytes ≤ (arg s 5).toNat * 8 := by
  have L := A.lengths
  have H := A.scratchLength
  unfold Spec.Dsa.lengthsValid at L
  unfold Spec.Dsa.scratchWords at H
  change 15712 ≤ _
  omega

theorem CheckingABI.stackArgument {s : State} (A : CheckingABI s) {i : Nat} (hi : i < 6) :
    StackArgument s (argumentPointer s 4) ((arg s 5).toNat * 8) i := by
  apply stackArgument_of (count := 6) (by have := A.stackBound; omega) hi
  · rw [A.rd, A.wr]; simp
  · exact A.scratchArgs.symm

theorem CheckingABI.stack {s : State} (A : CheckingABI s) :
    StkOk (s.gpr .esp) (argumentPointer s 4) ((arg s 5).toNat * 8) := by
  apply VG.Proof.Weierstrass.X86.stkOk_of (by decide : 20 ≤ 32) A.stackLow
  · have H := A.scratchBound
    simpa only [argumentPointer, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans (arg s 4).isLt (by decide : 2 ^ 32 < 2 ^ 64))] using H
  · have H : 15712 ≤ (arg s 5).toNat * 8 := A.used; omega
  · exact A.belowScratch

theorem CheckingABI.room {s : State} (A : CheckingABI s) :
    Pow.Room (s.gpr .esp) (argumentPointer s 4) ((arg s 5).toNat * 8) := by
  apply room_of A.stackLow
  · have H : 15712 ≤ (arg s 5).toNat * 8 := A.used; omega
  · exact A.belowScratch

end VG.Proof.Dsa.X86
