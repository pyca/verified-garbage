module

public import VerifiedGarbage.Proof.Rsa.X86.KcABI
import VerifiedGarbage.Proof.Weierstrass.X86.CallOps
import VerifiedGarbage.Proof.Dsa.X86.ABIResources
import VerifiedGarbage.Proof.Framework.Offset

/-! # The shared scratch allowance covers the native-word CRT arrays -/

@[expose] public section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Proof.Bignum.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.KeyCheck

theorem ABI.space {full : Bool} {s : State} (a : ABI full s) : arr (2 * (caller full s).n) nArr ≤ (caller full s).size := by
  have h := a.scratchLength
  have lo := a.lengths.1
  simp only [Spec.Rsa.scratchWords] at h
  simp only [caller, Spec.Rsa.modulusWords, arr, S, VG.Impl.Rsa.X86.Keys.hdr, nArr]
  omega

theorem ABI.used {full : Bool} {s : State} (a : ABI full s) : 160 ≤ (caller full s).size :=
  Nat.le_trans (Nat.le_add_right _ _) a.space

theorem ABI.width {full : Bool} {s : State} (a : ABI full s) : 8 ≤ (caller full s).n ∧ (caller full s).n ≤ 128 ∧
    (arg s 1).toNat ≤ 8 * (caller full s).n := by
  have lo := a.lengths.1; have hi := a.lengths.2
  simp only [caller, Spec.Rsa.modulusWords]
  omega

theorem ABI.stackArgument {full : Bool} {s : State} (a : ABI full s) {i : Nat} (hi : i < scratchArg full + 2) :
    StackArgument s (caller full s).base (caller full s).size i := by
  apply stackArgument_of (count := scratchArg full + 2) (by have := a.stackBound; omega) hi
  · rw [a.rd, a.wr]; simp
  · exact a.argsApart

theorem ABI.stack {full : Bool} {s : State} (a : ABI full s) : StkOk (s.gpr .esp) (caller full s).base (caller full s).size := by
  apply VG.Proof.Weierstrass.X86.stkOk_of (Nat.le_refl 20) a.stackLow
  · have h := a.scratchBound
    simpa only [caller, argumentPointer, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (Nat.lt_trans (arg s (scratchArg full)).isLt (by decide : 2 ^ 32 < 2 ^ 64))] using h
  · have := a.used; omega
  · exact a.belowScratch

theorem ABI.stackApart {full : Bool} {s : State} (a : ABI full s) {i : Nat} (hi : i < scratchArg full + 2)
    {r : Region} (hr : r ∈ (caller full s).writes) : (⟨stackAddress s i, 4⟩ : Region).Disjoint r := by
  apply (show (⟨argAddr s 0, 4 * (scratchArg full + 2)⟩ : Region).Disjoint r from by
    simp only [CallGeometry.writes, List.mem_singleton] at hr
    subst r
    exact a.argsApart).sub_left
  have p : stackAddress s i = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) :=
    addr_eq (by have := a.stackBound; omega)
  have z : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 :=
    addr_eq (by have := a.stackBound; omega)
  rw [p, z]
  exact Offset.sub _ (by omega) (by omega)

end VG.Proof.Rsa.X86.KeyCheck
