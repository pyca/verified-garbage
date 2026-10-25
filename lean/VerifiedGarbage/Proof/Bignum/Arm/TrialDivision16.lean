module

public import VerifiedGarbage.Impl.Bignum.Arm.TrialDivision16
public import VerifiedGarbage.Proof.X25519.Arm.Instr
public import VerifiedGarbage.Proof.RsaKeyGen.Trial16
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Omega

/-! Instruction proofs for the radix-2^16 trial reducer shared by RSA and FFDH. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.TrialDivision16
open VG VG.Arm VG.Proof.X25519.Arm VG.Proof.RsaKeyGen
open VG.Impl.Bignum.Arm.TrialDivision16

theorem lo16 (v : BitVec 32) : ((v <<< 16) >>> 16).toNat = v.toNat % 2 ^ 16 := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    show 2 ^ 32 = 2 ^ 16 * 2 ^ 16 by rfl, Nat.mul_mod_mul_right, Nat.mul_div_cancel _ (Nat.two_pow_pos 16)]

theorem hi16 (v : BitVec 32) : (v >>> 16).toNat = v.toNat / 2 ^ 16 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem newton_ok {u : State} {rest : List Instr} {Q : State → Prop}
    (k : ∀ u', Rest [.r4, .r5, .r6] u u' → u'.mem = u.mem →
      u'.gpr .r4 = nstep (u.gpr .r3) (u.gpr .r4) → WP isa (.block rest) u' Q) :
    WP isa (.block (newton ++ rest)) u Q := by
  simp only [newton, List.cons_append, List.nil_append]
  refine wp_mul fun u1 v1 => wp_mov (op2_imm (by decide)) fun u2 v2 => wp_dp (op2_reg _ _) fun u3 v3 =>
    wp_mul fun u4 v4 => k u4 ((v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
      (v4.rest (by decide))))) (by rw [v4.mem, v3.mem, v2.mem, v1.mem]) ?_
  rw [v4.gpr, v3.gpr, v3.other _ (by decide), dpVal, v2.gpr, v2.other _ (by decide), v2.other _ (by decide),
    v1.gpr, v1.other _ (by decide)]
  rfl

theorem redc_ok {u : State} {h acc s sv : Nat} (r5 : (u.gpr .r5).toNat = h) (hh : h < 2 ^ 16)
    (r2 : u.gpr .r2 = BitVec.ofNat 32 acc) (hacc : acc < 2 * s) (r4 : (u.gpr .r4).toNat = sv)
    (r3 : u.gpr .r3 = BitVec.ofNat 32 s) (hs : 3 ≤ s ∧ s < 8162) (hinv : (s * sv + 1) % 2 ^ 16 = 0)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ u', Rest [.r2, .r5, .r6] u u' → u'.mem = u.mem →
      (∀ a', a' < 2 * s → a' * 2 ^ 16 % s = (h + acc) % s → u'.gpr .r2 = BitVec.ofNat 32 a' →
        WP isa (.block rest) u' Q)) :
    WP isa (.block (redc ++ rest)) u Q := by
  simp only [redc, redcAt, List.cons_append, List.nil_append]
  refine wp_dp (op2_reg _ _) fun u1 v1 => wp_mul fun u2 v2 => wp_mov (op2_lsl (by decide)) fun u3 v3 =>
    wp_mov (op2_lsr (by decide)) fun u4 v4 => wp_mul fun u5 v5 => wp_dp (op2_reg _ _) fun u6 v6 =>
      wp_mov (op2_lsr (by decide)) fun u7 v7 => ?_
  have k7 : Rest [.r2, .r5, .r6] u u7 := (v1.rest (by decide)).trans ((v2.rest (by decide)).trans
    ((v3.rest (by decide)).trans ((v4.rest (by decide)).trans ((v5.rest (by decide)).trans ((v6.rest (by decide)).trans
      (v7.rest (by decide)))))))
  have m7 : u7.mem = u.mem := by rw [v7.mem, v6.mem, v5.mem, v4.mem, v3.mem, v2.mem, v1.mem]
  have ha : acc < 2 ^ 32 := by omega
  -- `X = h + acc`, `q = X sv mod 2^16`.
  have x1 : (u1.gpr .r5).toNat = h + acc := by
    rw [v1.gpr, dpVal, BitVec.toNat_add, r5, r2, toNat_imm ha]; omega
  have sv16 : sv < 2 ^ 16 ∨ True := .inr trivial
  have q4 : (u4.gpr .r6).toNat = (h + acc) * sv % 2 ^ 16 := by
    rw [v4.gpr, v3.gpr, lo16, v2.gpr, BitVec.toNat_mul, x1, v1.other _ (by decide), r4,
      Nat.mod_mod_of_dvd _ (by decide)]
  have hq := Nat.mod_lt ((h + acc) * sv) (Nat.two_pow_pos 16)
  have s5 : (u5.gpr .r6).toNat = (h + acc) * sv % 2 ^ 16 * s := by
    rw [v5.gpr, BitVec.toNat_mul, q4, v4.other _ (by decide), v3.other _ (by decide), v2.other _ (by decide),
      v1.other _ (by decide), r3, toNat_imm (by omega)]
    apply Nat.mod_eq_of_lt
    have : (h + acc) * sv % 2 ^ 16 * s < 2 ^ 16 * 8162 := Nat.mul_lt_mul'' hq hs.2
    omega
  have x5 : (u5.gpr .r5).toNat = h + acc := by
    rw [v5.other _ (by decide), v4.other _ (by decide), v3.other _ (by decide), v2.other _ (by decide), x1]
  have s6 : (u6.gpr .r6).toNat = h + acc + (h + acc) * sv % 2 ^ 16 * s := by
    rw [v6.gpr, dpVal, BitVec.toNat_add, s5, x5]
    have : (h + acc) * sv % 2 ^ 16 * s < 2 ^ 16 * 8162 := Nat.mul_lt_mul'' hq hs.2
    omega
  obtain ⟨_, hlt, hcong⟩ := redc16_math (X := h + acc) (s := s) (sv := sv) hinv (by
    have : 3 * 2 ^ 16 ≤ s * 2 ^ 16 := Nat.mul_le_mul_right _ hs.1
    omega)
  refine k u7 k7 m7 _ hlt hcong ?_
  apply BitVec.eq_of_toNat_eq
  rw [v7.gpr, hi16, s6, toNat_imm (by omega)]

end VG.Proof.Bignum.Arm.TrialDivision16
