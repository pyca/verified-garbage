module

public import VerifiedGarbage.Proof.Poly1305.RISCV64.Absorb
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Poly1305 on RISC-V: the final reduction

`reduce_ok`: `reduce` leaves the accumulator modulo `p`, as on AArch64
(`Proof/Poly1305/AArch64/Radix64/Reduce.lean`): `g = h + 5` is selected if it
reaches `2¹³⁰`.
-/

@[expose] public section

namespace VG.Proof.Poly1305.RISCV64

open VG VG.RISCV64 VG.RISCV64.Wide VG.Impl.Poly1305.RISCV64
open VG.Spec.Poly1305 (P)

theorem select_keep (x y : BitVec 64) : y ^^^ ((x ^^^ y) &&& ((0 : BitVec 64) + BitVec.ofInt 64 (-1))) = x := by
  rw [show (0 : BitVec 64) + BitVec.ofInt 64 (-1) = BitVec.allOnes 64 by decide, BitVec.and_allOnes,
    ← BitVec.xor_assoc, BitVec.xor_comm y x, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem select_take (x y : BitVec 64) : y ^^^ ((x ^^^ y) &&& ((1 : BitVec 64) + BitVec.ofInt 64 (-1))) = y := by
  rw [show (1 : BitVec 64) + BitVec.ofInt 64 (-1) = 0 by decide]
  simp

theorem reduce_eq : reduce = plus5 ++ (mask ++
    (selectLimb H0 X0 ++ selectLimb H1 X1 ++ selectLimb H2 Y0)) := by
  simp only [reduce, List.append_assoc]

theorem plus5_ok (s : State) :
    WP isa (.block plus5) s fun s' =>
      val3 s' X0 X1 Y0 = (hv s + 5) % 2 ^ 192 ∧ Keeps [T1, X0, X1, Y0, T1] s s' := by
  refine WP.block_cons_iff.mpr ⟨_, exec_li (show imm12 5 by decide), ?_⟩
  refine WP.mono addW3_ok fun s' ⟨e, k⟩ => ⟨?_, ((Keeps.refl [T1] s).write _ (by decide)).trans k⟩
  rw [e]
  simp only [val3, hv, RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false]
  rfl

theorem mask_ok (s : State) :
    WP isa (.block mask) s fun s' =>
      s'.gpr T1 = (s.gpr Y0 >>> 2) + BitVec.ofInt 64 (-1) ∧
      s'.gpr Y0 = s.gpr Y0 &&& BitVec.ofInt 64 3 ∧ Keeps [T1, Y0] s s' := by
  apply WP.of_runBlock
  simp only [mask, runBlock_cons, runStep_some, runBlock_nil, exec_shift_d (show 2 < 64 by decide),
    exec_addi (show imm12 (-1) by decide), exec_logicImm (show imm12 3 by decide),
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, (((Keeps.refl _ s).write _ (by decide)).write _ (by decide)).write _ (by decide)⟩
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false]
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false]

theorem select_ok (s : State) :
    WP isa (.block (selectLimb H0 X0 ++ selectLimb H1 X1 ++ selectLimb H2 Y0)) s fun s' =>
      s'.gpr H0 = s.gpr X0 ^^^ ((s.gpr H0 ^^^ s.gpr X0) &&& s.gpr T1) ∧
      s'.gpr H1 = s.gpr X1 ^^^ ((s.gpr H1 ^^^ s.gpr X1) &&& s.gpr T1) ∧
      s'.gpr H2 = s.gpr Y0 ^^^ ((s.gpr H2 ^^^ s.gpr Y0) &&& s.gpr T1) ∧
      Keeps [H0, H1, H2, T2] s s' := by
  apply WP.of_runBlock
  simp only [selectLimb, List.cons_append, List.nil_append, runBlock_cons, runStep_some,
    runBlock_nil, exec_logic, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false]
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false]
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false]
  · exact (((((((((Keeps.refl _ s).write _ (by decide)).write _ (by decide)).write _
      (by decide)).write _ (by decide)).write _ (by decide)).write _ (by decide)).write _
      (by decide)).write _ (by decide)).write _ (by decide)

theorem reduce_ok (s : State) :
    WP isa (.block reduce) s fun s' =>
      ((s.gpr H2).toNat ≤ 4 → hv s' = hv s % P) ∧
      Keeps [H0, H1, H2, X0, X1, Y0, T1, T2] s s' := by
  have g0 := (s.gpr H0).isLt; have g1 := (s.gpr H1).isLt
  rw [reduce_eq]
  refine WP.block_append (WP.mono (plus5_ok s) fun s₁ ⟨e₁, k₁⟩ => ?_)
  refine WP.block_append (WP.mono (mask_ok s₁) fun s₂ ⟨m₁, m₂, k₂⟩ => ?_)
  refine WP.mono (select_ok s₂) fun s₃ ⟨c₁, c₂, c₃, k₃⟩ => ?_
  refine ⟨fun hh2 => ?_, ((k₁.trans k₂).trans k₃).mono⟩
  have hv5 : hv s + 5 < 2 ^ 192 := by simp only [hv, val3]; omega_using [g0, g1, hh2]
  rw [Nat.mod_eq_of_lt hv5] at e₁
  simp only [val3] at e₁
  have ga := (s₁.gpr X0).isLt; have gd := (s₁.gpr X1).isLt
  have hg2 : (s₁.gpr Y0).toNat ≤ 5 := by simp only [hv, val3] at e₁; omega_using [g0, g1, hh2, e₁, ga, gd]
  have k₁₂ := k₁.trans k₂
  rw [k₁₂.gpr' (r := H0), k₂.gpr' (r := X0), m₁] at c₁
  rw [k₁₂.gpr' (r := H1), k₂.gpr' (r := X1), m₁] at c₂
  rw [k₁₂.gpr' (r := H2), m₂, m₁] at c₃
  have ht : (s₁.gpr Y0 >>> 2).toNat = (s₁.gpr Y0).toNat / 4 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  simp only [hv, val3, c₁, c₂, c₃]
  simp only [hv, val3] at e₁
  have hP : P = 2 ^ 130 - 5 := rfl
  by_cases hge : 4 ≤ (s₁.gpr Y0).toNat
  · have h1 : s₁.gpr Y0 >>> 2 = 1 := BitVec.eq_of_toNat_eq (by
      rw [ht]; show _ = 1; omega_using [hg2, hge])
    rw [h1, select_take, select_take, select_take, and3_toNat']
    have ge : P ≤ (s.gpr H0).toNat + 2 ^ 64 * (s.gpr H1).toNat + 2 ^ 128 * (s.gpr H2).toNat := by
      omega_using [e₁, hg2, hP, hge, ga, gd]
    have lt : (s.gpr H0).toNat + 2 ^ 64 * (s.gpr H1).toNat + 2 ^ 128 * (s.gpr H2).toNat - P <
        P := by omega_using [g0, g1, hh2, e₁, hP, ge]
    rw [Nat.mod_eq_sub_mod ge, Nat.mod_eq_of_lt lt]
    omega_using [g0, g1, hh2, e₁, hP, ge, lt, ga, gd, hge, hg2]
  · have h0 : s₁.gpr Y0 >>> 2 = 0 := BitVec.eq_of_toNat_eq (by
      rw [ht]; show _ = 0; omega_using [hg2, hge])
    have lt : (s.gpr H0).toNat + 2 ^ 64 * (s.gpr H1).toNat + 2 ^ 128 * (s.gpr H2).toNat <
        P := by omega_using [e₁, hg2, hP, hge, ga, gd]
    rw [h0, select_keep, select_keep, select_keep, Nat.mod_eq_of_lt lt]

end VG.Proof.Poly1305.RISCV64
