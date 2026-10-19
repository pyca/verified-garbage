module

public import VerifiedGarbage.Proof.Rsa.X86.RvABI
import VerifiedGarbage.Proof.Weierstrass.X86.CallOps

/-! # The shared scratch allowance covers the native-word recovery arrays -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Proof.Bignum.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Recover

theorem ABI.space {s : State} (a : ABI s) : arr (2 * (caller s).n + 2) nArr ≤ (caller s).Z := by
  have h := a.scratchLength
  have lo := a.lengths.1
  simp only [Spec.Rsa.scratchWords] at h
  simp only [caller, Spec.Rsa.modulusWords, arr, S, VG.Impl.Rsa.X86.Keys.hdr, nArr]
  omega

theorem ABI.used {s : State} (a : ABI s) : 160 ≤ (caller s).Z :=
  Nat.le_trans (Nat.le_add_right _ _) a.space

theorem ABI.width {s : State} (a : ABI s) : 8 ≤ (caller s).n ∧ (caller s).n ≤ 128 ∧
    (arg s 5).toNat ≤ 8 * (caller s).n := by
  have lo := a.lengths.1; have hi := a.lengths.2
  simp only [caller, Spec.Rsa.modulusWords]
  omega

theorem ABI.stackArgument {s : State} (a : ABI s) {i : Nat} (hi : i < 12) :
    StackArgument s (caller s).B (caller s).Z i := by
  apply stackArgument_of (count := 12) (by have := a.stackBound; omega) hi
  · rw [a.rd, a.wr]; simp
  · exact a.argsApart _ (by simp [CallGeometry.writes])

theorem ABI.stack {s : State} (a : ABI s) : StkOk (s.gpr .esp) (caller s).B (caller s).Z := by
  apply VG.Proof.Weierstrass.X86.stkOk_of (Nat.le_refl 20) a.stackLow
  · have h := a.scratchBound
    simpa only [caller, argumentPointer, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (Nat.lt_trans (arg s 10).isLt (by decide : 2 ^ 32 < 2 ^ 64))] using h
  · have := a.used; omega
  · exact a.belowScratch

theorem ABI.stackApart {s : State} (a : ABI s) {i : Nat} (hi : i < 12)
    {r : Region} (hr : r ∈ (caller s).writes) : (⟨stackAddress s i, 4⟩ : Region).Disjoint r := by
  apply (a.argsApart r hr).sub_left
  have p : stackAddress s i = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) :=
    addr_eq (by have := a.stackBound; omega)
  have z : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 :=
    addr_eq (by have := a.stackBound; omega)
  rw [p, z]
  exact Offset.sub _ (by omega) (by omega)

theorem ABI.lengths_ok {s : State} (a : ABI s) : Lengths (caller s) :=
  ⟨a.lengths.1, a.lengths.2, rfl,
    BitVec.eq_of_toNat_eq a.pLen, BitVec.eq_of_toNat_eq a.qLen⟩

end VG.Proof.Rsa.X86.Recover
