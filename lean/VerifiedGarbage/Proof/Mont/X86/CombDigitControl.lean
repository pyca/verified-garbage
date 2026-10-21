module

public import VerifiedGarbage.Proof.Mont.X86.CombTooth
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! Accumulate five extracted bits without value-dependent control flow. -/

@[expose] public section
namespace VG.Proof.Mont.X86.Comb
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Comb
open VG.Proof.Mont VG.Proof.Mont.X86

theorem doubleBits_ok (j : Nat) {s : State} (bound : (s.gpr .eax).toNat*2^j<2^32) :
    WP isa (.block (List.replicate j (.alu .add .eax (.reg .eax)))) s fun t =>
      t.mem=s.mem ∧ (t.gpr .eax).toNat=(s.gpr .eax).toNat*2^j ∧ Keeps [.eax] s t := by
  induction j generalizing s with
  | zero => exact WP.block_nil ⟨rfl,by simp only [Nat.pow_zero,Nat.mul_one],Keeps.refl _ _⟩
  | succ j ih =>
    rw [List.replicate_succ]
    refine wp_addS rfl fun u U _ => ?_
    have eq : (u.gpr .eax).toNat=(s.gpr .eax).toNat*2 := by
      rw [U.gpr,BitVec.toNat_add,Nat.mod_eq_of_lt]
      · omega
      · have pow : 2≤2^(j+1) := Nat.le_self_pow (by omega) 2
        have := Nat.mul_le_mul_left (s.gpr .eax).toNat pow
        omega
    have next : (u.gpr .eax).toNat*2^j=(s.gpr .eax).toNat*2^(j+1) := by
      rw [eq,Nat.pow_succ]; ac_rfl
    exact WP.mono (ih (by rw [next]; exact bound)) fun t ⟨M,V,K⟩ =>
      ⟨M.trans U.mem,V.trans next,(U.keeps.mono (by decide)).trans K⟩

theorem addBit_ok {s : State} {j b a : Nat} (hj : j<5) (hb : b<2) (ha : a<2^j)
    (A : (s.gpr .eax).toNat=b) (B : (s.gpr .ebx).toNat=a) :
    WP isa (.block (List.replicate j (.alu .add .eax (.reg .eax)) ++ [.alu .or .ebx (.reg .eax)])) s
      fun t => t.mem=s.mem ∧ (t.gpr .ebx).toNat=a+b*2^j ∧ Keeps [.eax,.ebx] s t := by
  have p32 : 2^j ≤ 16 := by
    have finite : ∀ j<5, 2^j≤16 := by decide
    exact finite j hj
  refine WP.block_append (WP.mono (doubleBits_ok j (by rw [A]; have := Nat.mul_le_mul_right (2^j) (show b≤1 by omega); omega))
    fun u ⟨M,V,K⟩ => ?_)
  refine wp_or fun t T => WP.block_nil ⟨T.mem.trans M,?_,(K.mono (by decide)).trans (T.keeps.mono (by decide))⟩
  rw [T.gpr,BitVec.toNat_or,K.1 .ebx (by decide),B,V,A,Nat.or_comm]
  rw [←Nat.shiftLeft_eq,←Nat.shiftLeft_add_eq_or_of_lt ha,Nat.shiftLeft_eq,Nat.add_comm]

end VG.Proof.Mont.X86.Comb
