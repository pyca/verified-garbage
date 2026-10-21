module
public import VerifiedGarbage.Proof.Dsa.X86.DerivingABI
import VerifiedGarbage.Proof.Weierstrass.X86.CallOps
public import VerifiedGarbage.Proof.Dsa.X86.StackArgument
public import VerifiedGarbage.Proof.Dsa.X86.StackFrame
import VerifiedGarbage.Proof.Dsa.X86.ABIResources

/-! # Stack and workspace resources of key derivation -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem DerivingABI.used {s : State} (A : DerivingABI s) : usedBytes ≤ (arg s 8).toNat * 8 := by
  have L := A.lengths
  have H := A.scratchLength
  unfold Spec.Dsa.lengthsValid at L
  unfold Spec.Dsa.scratchWords at H
  change 15712 ≤ _
  omega

theorem DerivingABI.stackArgument {s : State} (A : DerivingABI s) {i : Nat} (hi : i < 9) :
    StackArgument s (argumentPointer s 7) ((arg s 8).toNat * 8) i := by
  apply stackArgument_of (count := 9) (by have := A.stackBound; omega) hi
  · rw [A.rd, A.wr]; simp
  · exact A.scratchArgs.symm

theorem DerivingABI.stack {s : State} (A : DerivingABI s) :
    StkOk (s.gpr .esp) (argumentPointer s 7) ((arg s 8).toNat * 8) := by
  apply VG.Proof.Weierstrass.X86.stkOk_of (by decide : 20 ≤ 32) A.stackLow
  · have H := A.scratchBound
    simpa only [argumentPointer, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans (arg s 7).isLt (by decide : 2 ^ 32 < 2 ^ 64))] using H
  · have H : 15712 ≤ (arg s 8).toNat * 8 := A.used; omega
  · exact A.belowScratch

theorem DerivingABI.room {s : State} (A : DerivingABI s) :
    Pow.Room (s.gpr .esp) (argumentPointer s 7) ((arg s 8).toNat * 8) := by
  apply room_of A.stackLow
  · have H : 15712 ≤ (arg s 8).toNat * 8 := A.used; omega
  · exact A.belowScratch

end VG.Proof.Dsa.X86
