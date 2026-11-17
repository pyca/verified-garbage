module

public import VerifiedGarbage.Proof.Dsa.X86.StackFrame
public import VerifiedGarbage.Proof.Dsa.X86.StackArgument
public import VerifiedGarbage.Proof.Weierstrass.PointContract
import VerifiedGarbage.Proof.Weierstrass.X86.CallOps
import VerifiedGarbage.Proof.Framework.Offset
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Dsa.X86.VerifyingABI
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Spec.Weierstrass

/-! ### `Dsa.X86.SigningABI`, which this module and modules that import it used -/

section

/-! # Signing resources supplied by the shared cdecl contract -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86

structure SigningABI (s : State) : Prop where
  stackLow : 108 ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 48 ≤ 2 ^ 32
  rd : s.rd = [⟨argumentPointer s 2, (arg s 3).toNat⟩,
    ⟨argumentPointer s 5, (arg s 6).toNat⟩, ⟨argumentPointer s 7, (arg s 8).toNat⟩]
  wr : s.wr = [⟨argumentPointer s 0, (arg s 1).toNat⟩, ⟨argumentPointer s 9, (arg s 10).toNat * 8⟩, ⟨argAddr s 0, 44⟩]
  outScratch : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint
    ⟨argumentPointer s 9, (arg s 10).toNat * 8⟩
  retOut : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint
    ⟨argumentPointer s 0, (arg s 1).toNat⟩
  outBound : (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32
  keyScratch : (⟨argumentPointer s 2, (arg s 3).toNat⟩ : Region).Disjoint
    ⟨argumentPointer s 9, (arg s 10).toNat * 8⟩
  nonceScratch : (⟨argumentPointer s 5, (arg s 6).toNat⟩ : Region).Disjoint
    ⟨argumentPointer s 9, (arg s 10).toNat * 8⟩
  digestScratch : (⟨argumentPointer s 7, (arg s 8).toNat⟩ : Region).Disjoint
    ⟨argumentPointer s 9, (arg s 10).toNat * 8⟩
  scratchArgs : (⟨argumentPointer s 9, (arg s 10).toNat * 8⟩ : Region).Disjoint ⟨argAddr s 0, 44⟩
  retScratch : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint
    ⟨argumentPointer s 9, (arg s 10).toNat * 8⟩
  belowScratch : (⟨(s.gpr .esp).setWidth 64 - 108#64, 108⟩ : Region).Disjoint
    ⟨argumentPointer s 9, (arg s 10).toNat * 8⟩
  belowKey : (⟨(s.gpr .esp).setWidth 64 - 108#64, 108⟩ : Region).Disjoint
    ⟨argumentPointer s 2, (arg s 3).toNat⟩
  belowNonce : (⟨(s.gpr .esp).setWidth 64 - 108#64, 108⟩ : Region).Disjoint
    ⟨argumentPointer s 5, (arg s 6).toNat⟩
  belowDigest : (⟨(s.gpr .esp).setWidth 64 - 108#64, 108⟩ : Region).Disjoint
    ⟨argumentPointer s 7, (arg s 8).toNat⟩
  keyBound : (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32
  nonceBound : (arg s 5).toNat + (arg s 6).toNat ≤ 2 ^ 32
  digestBound : (arg s 7).toNat + (arg s 8).toNat ≤ 2 ^ 32
  scratchBound : (arg s 9).toNat + (arg s 10).toNat * 8 ≤ 2 ^ 32
  lengths : Spec.Dsa.lengthsValid (arg s 4).toNat (arg s 6).toNat
  keyLength : (arg s 3).toNat = 3 * (arg s 4).toNat + 2 * (arg s 6).toNat
  outLength : (arg s 1).toNat = 2 * (arg s 6).toNat
  scratchLength : Spec.Dsa.scratchWords (arg s 4).toNat ≤ (arg s 10).toNat

theorem signingABI_of {s : State} (h : (Spec.Dsa.signContract abi 108).pre s) : SigningABI s := by
  sig_pre [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argSlots, argVal, argBytes, stackBelow] at h
  sig_split h
  constructor <;> with_reducible assumption

end VG.Proof.Dsa.X86

end

end

/-! # Stack and scratch resources for the cdecl entry programs -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem stackValue_arg (s : State) (i : Nat) : stackValue s i = arg s i := rfl

theorem stackArgument_of {s : State} {base : Addr} {size count i : Nat}
    (bound : (s.gpr .esp).toNat + 4 + 4 * count ≤ 2 ^ 32) (hi : i < count)
    (mem : (⟨argAddr s 0, 4 * count⟩ : Region) ∈ s.rd ++ s.wr)
    (apart : Region.Disjoint ⟨argAddr s 0, 4 * count⟩ ⟨base, size⟩) :
    StackArgument s base size i := by
  have P : stackAddress s i = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) :=
    addr_eq (by omega_using [bound, hi])
  have Z : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 := addr_eq (by omega_using [bound, hi])
  refine ⟨⟨_, mem, ?_⟩, apart.sub_left ?_⟩
  · rw [P, Z]
    exact Offset.contains _ (by omega_using []) (by omega_using [hi]) (by omega_using [bound])
  · rw [P, Z]
    exact Offset.sub _ (by omega_using []) (by omega_using [hi])

theorem VerifyingABI.used {s : State} (A : VerifyingABI s) : usedBytes ≤ (arg s 9).toNat * 8 := by
  have L := A.lengths
  have H := A.scratchLength
  unfold Spec.Dsa.lengthsValid at L
  unfold Spec.Dsa.scratchWords at H
  change 15712 ≤ _
  omega_using [L, H]

theorem SigningABI.used {s : State} (A : SigningABI s) : usedBytes ≤ (arg s 10).toNat * 8 := by
  have L := A.lengths
  have H := A.scratchLength
  unfold Spec.Dsa.lengthsValid at L
  unfold Spec.Dsa.scratchWords at H
  change 15712 ≤ _
  omega_using [L, H]

theorem VerifyingABI.stackArgument {s : State} (A : VerifyingABI s) {i : Nat} (hi : i < 10) :
    StackArgument s (argumentPointer s 8) ((arg s 9).toNat * 8) i := by
  apply stackArgument_of (count := 10) (by have := A.stackBound; omega_using [this]) hi
  · rw [A.rd, A.wr]; simp
  · exact A.scratchArgs.symm

theorem SigningABI.stackArgument {s : State} (A : SigningABI s) {i : Nat} (hi : i < 11) :
    StackArgument s (argumentPointer s 9) ((arg s 10).toNat * 8) i := by
  apply stackArgument_of (count := 11) (by have := A.stackBound; omega_using [this]) hi
  · rw [A.rd, A.wr]; simp
  · exact A.scratchArgs.symm

theorem room_of {sp : BitVec 32} {base : Addr} {size : Nat} (hsp : 108 ≤ sp.toNat)
    (hs : 0 < size)
    (hd : Region.Disjoint ⟨sp.setWidth 64 - 108#64, 108⟩ ⟨base, size⟩) : Pow.Room sp base size := by
  refine ⟨hsp, ?_⟩
  by_contra h
  simp only [not_or, Nat.not_le] at h
  have hb := sp.isLt
  by_cases hc : base.toNat + 108 ≤ sp.toNat
  · refine hd (sp.setWidth 64 - 108#64) ?_ ?_
    · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_using []
    · simp only [Region.Contains]; bv_omega
  · refine hd base ?_ ?_
    · simp only [Region.Contains]; bv_omega
    · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_using [hs]

theorem callStack_eq {sp : BitVec 32} (h : 108 ≤ sp.toNat) :
    callStack sp = ⟨sp.setWidth 64 - 108#64, 108⟩ := by
  unfold callStack
  rw [VG.X86.Taint.sub_setWidth h]

theorem VerifyingABI.stack {s : State} (A : VerifyingABI s) :
    StkOk (s.gpr .esp) (argumentPointer s 8) ((arg s 9).toNat * 8) := by
  apply VG.Proof.Weierstrass.X86.stkOk_of (by decide : 20 ≤ 108) A.stackLow
  · have H := A.scratchBound
    simpa only [argumentPointer, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans (arg s 8).isLt (by decide : 2 ^ 32 < 2 ^ 64))] using H
  · have H : 15712 ≤ (arg s 9).toNat * 8 := A.used; omega_using [H]
  · exact A.belowScratch

theorem SigningABI.stack {s : State} (A : SigningABI s) :
    StkOk (s.gpr .esp) (argumentPointer s 9) ((arg s 10).toNat * 8) := by
  apply VG.Proof.Weierstrass.X86.stkOk_of (by decide : 20 ≤ 108) A.stackLow
  · have H := A.scratchBound
    simpa only [argumentPointer, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans (arg s 9).isLt (by decide : 2 ^ 32 < 2 ^ 64))] using H
  · have H : 15712 ≤ (arg s 10).toNat * 8 := A.used; omega_using [H]
  · exact A.belowScratch

theorem VerifyingABI.room {s : State} (A : VerifyingABI s) :
    Pow.Room (s.gpr .esp) (argumentPointer s 8) ((arg s 9).toNat * 8) := by
  apply room_of A.stackLow
  · have H : 15712 ≤ (arg s 9).toNat * 8 := A.used; omega_using [H]
  · exact A.belowScratch

theorem SigningABI.room {s : State} (A : SigningABI s) :
    Pow.Room (s.gpr .esp) (argumentPointer s 9) ((arg s 10).toNat * 8) := by
  apply room_of A.stackLow
  · have H : 15712 ≤ (arg s 10).toNat * 8 := A.used; omega_using [H]
  · exact A.belowScratch

end VG.Proof.Dsa.X86
