module

public import VerifiedGarbage.Impl.Bignum.Arm.TrialDivision16
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.RsaKeyGen.Table
public import VerifiedGarbage.Proof.Framework.PowLit

/-! ### `RsaKeyGen.Trial16`, which this module and modules that import it used -/

section

/-!
# A candidate for an RSA prime: trial division by 16-bit halves

For 32-bit targets, trial division reduces the candidate `c` by Montgomery
reduction of its 16-bit halves, `acc := (acc + h) 2^(−16) mod s`
(`redc16_math`), with `−s⁻¹ mod 2^16` from three steps of Newton's
iteration on 32-bit words (`ninv`, `ninv_tab` for every entry of the
table): after a 32-bit word `x`, `acc 2^32 ≡ x + acc` (`trial_word16`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen

open VG.Impl.RsaKeyGen

/-- One step of Newton's iteration for `s⁻¹`, on 32-bit words. -/
def nstep (s x : BitVec 32) : BitVec 32 := x * (2 - s * x)

/-- `−s⁻¹ mod 2^16` for an odd `s`, as the 32-bit code computes it. -/
def ninv (s : BitVec 32) : BitVec 32 := ((0 - nstep s (nstep s (nstep s s))) <<< 16) >>> 16

theorem slots_ninv : slots.all (fun s => (s * (ninv (BitVec.ofNat 32 s)).toNat + 1) % 2 ^ 16 == 0) = true := by
  unfold slots; rw [primes.lit_eq]; decide +kernel

/-- `ninv` of every entry of the table is `−s⁻¹ mod 2^16`. -/
theorem ninv_tab {i : Nat} (hi : i < 1024) :
    (tabEntry i * (ninv (BitVec.ofNat 32 (tabEntry i))).toNat + 1) % 2 ^ 16 = 0 := by
  have h := List.all_eq_true.mp slots_ninv (slots[i]'(by rw [slots_length]; exact hi)) (List.getElem_mem _)
  simp only [beq_iff_eq] at h
  have : tabEntry i = slots[i]'(by rw [slots_length]; exact hi) := by
    unfold tabEntry; exact getD_of_lt _
  rw [this]; exact h

/-- Montgomery reduction by `2^16` modulo `s`, with `sv = −s⁻¹ mod 2^16`, of
`X < s 2^16`: exact, below `2 s`, and `X 2^(−16) mod s`. -/
theorem redc16_math {X s sv : Nat} (hinv : (s * sv + 1) % 2 ^ 16 = 0) (hX : X < s * 2 ^ 16) :
    (X + X * sv % 2 ^ 16 * s) % 2 ^ 16 = 0 ∧
    (X + X * sv % 2 ^ 16 * s) / 2 ^ 16 < 2 * s ∧
    ((X + X * sv % 2 ^ 16 * s) / 2 ^ 16 * 2 ^ 16) % s = X % s := by
  have hd : (X + X * sv % 2 ^ 16 * s) % 2 ^ 16 = 0 := by
    have h16 : 2 ^ 16 ∣ s * sv + 1 := Nat.dvd_of_mod_eq_zero hinv
    have hq := Nat.div_add_mod (X * sv) (2 ^ 16)
    have : X + X * sv % 2 ^ 16 * s + 2 ^ 16 * (X * sv / 2 ^ 16) * s = X * (s * sv + 1) := by
      rw [Nat.add_assoc, ← Nat.add_mul, Nat.add_comm (X * sv % 2 ^ 16), hq, Nat.mul_add, Nat.mul_one,
        Nat.add_comm, Nat.mul_assoc, Nat.mul_comm sv s]
    have h2 : 2 ^ 16 ∣ X + X * sv % 2 ^ 16 * s + 2 ^ 16 * (X * sv / 2 ^ 16) * s := by
      rw [this]; exact Nat.dvd_mul_left_of_dvd h16 X
    have h3 : 2 ^ 16 ∣ 2 ^ 16 * (X * sv / 2 ^ 16) * s := Nat.dvd_mul_right_of_dvd (Nat.dvd_mul_right _ _) _
    exact Nat.mod_eq_zero_of_dvd ((Nat.dvd_add_right h3).mp (by rwa [Nat.add_comm] at h2))
  have hu : X * sv % 2 ^ 16 < 2 ^ 16 := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hexact : (X + X * sv % 2 ^ 16 * s) / 2 ^ 16 * 2 ^ 16 = X + X * sv % 2 ^ 16 * s := by
    have := Nat.div_add_mod (X + X * sv % 2 ^ 16 * s) (2 ^ 16)
    rw [hd, Nat.add_zero, Nat.mul_comm] at this; exact this
  refine ⟨hd, ?_, ?_⟩
  · have hus : X * sv % 2 ^ 16 * s < 2 ^ 16 * s := Nat.mul_lt_mul_of_pos_right hu (by
      rcases Nat.eq_zero_or_pos s with h | h
      · rw [h, Nat.zero_mul] at hX; omega_using [hX]
      · exact h)
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
    rw [Nat.mul_comm s (2 ^ 16)] at hX
    calc X + X * sv % 2 ^ 16 * s < 2 ^ 16 * s + 2 ^ 16 * s := Nat.add_lt_add hX hus
      _ = 2 * s * 2 ^ 16 := by rw [← Nat.two_mul, Nat.mul_comm (2 ^ 16) s, ← Nat.mul_assoc]
  · rw [hexact, Nat.add_mul_mod_self_right]

/-- Two reductions of a 32-bit word's halves: `acc 2^(32 j) ≡ c_j` carries on
to `j + 1` words. -/
theorem trial_word16 {s acc r1 r2 x V j : Nat} (h1 : r1 * 2 ^ 16 % s = (x % 2 ^ 16 + acc) % s)
    (h2 : r2 * 2 ^ 16 % s = (x / 2 ^ 16 + r1) % s) (hV : acc * 2 ^ (32 * j) % s = V % s) :
    r2 * 2 ^ (32 * (j + 1)) % s = (V + 2 ^ (32 * j) * x) % s := by
  have mr : ∀ {a b : Nat} (c : Nat), a % s = b % s → a * c % s = b * c % s := fun c h => by
    rw [Nat.mul_mod, h, ← Nat.mul_mod]
  have ml : ∀ {a b : Nat} (c : Nat), a % s = b % s → (c + a) % s = (c + b) % s := fun c h => by
    rw [Nat.add_mod, h, ← Nat.add_mod]
  have e3 : r2 * 2 ^ 32 % s = (x + acc) % s := by
    have : r2 * 2 ^ 32 = r2 * 2 ^ 16 * 2 ^ 16 := by rw [Nat.mul_assoc, ← Nat.pow_add]
    rw [this, ← Nat.mod_mul_mod, h2, Nat.mod_mul_mod, Nat.add_mul, ml _ h1, ← Nat.add_assoc,
      Nat.mul_comm (x / 2 ^ 16), Nat.add_comm (2 ^ 16 * (x / 2 ^ 16)), Nat.mod_add_div]
  have : r2 * 2 ^ (32 * (j + 1)) = r2 * 2 ^ 32 * 2 ^ (32 * j) := by
    rw [Nat.mul_assoc, ← Nat.pow_add]; congr 2; omega_using []
  rw [this, mr _ e3, Nat.add_mul, ml _ hV, Nat.add_comm, Nat.mul_comm x]

end VG.Proof.RsaKeyGen

end

end

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
  have ha : acc < 2 ^ 32 := by omega_using [hacc, hs]
  -- `X = h + acc`, `q = X sv mod 2^16`.
  have x1 : (u1.gpr .r5).toNat = h + acc := by
    rw [v1.gpr, dpVal, BitVec.toNat_add, r5, r2, toNat_imm ha]; omega_using [hh, hacc, hs]
  have sv16 : sv < 2 ^ 16 ∨ True := .inr trivial
  have q4 : (u4.gpr .r6).toNat = (h + acc) * sv % 2 ^ 16 := by
    rw [v4.gpr, v3.gpr, lo16, v2.gpr, BitVec.toNat_mul, x1, v1.other _ (by decide), r4,
      Nat.mod_mod_of_dvd _ (by decide)]
  have hq := Nat.mod_lt ((h + acc) * sv) (Nat.two_pow_pos 16)
  have s5 : (u5.gpr .r6).toNat = (h + acc) * sv % 2 ^ 16 * s := by
    rw [v5.gpr, BitVec.toNat_mul, q4, v4.other _ (by decide), v3.other _ (by decide), v2.other _ (by decide),
      v1.other _ (by decide), r3, toNat_imm (by omega_using [hs])]
    apply Nat.mod_eq_of_lt
    have : (h + acc) * sv % 2 ^ 16 * s < 2 ^ 16 * 8162 := Nat.mul_lt_mul'' hq hs.2
    omega_using [this]
  have x5 : (u5.gpr .r5).toNat = h + acc := by
    rw [v5.other _ (by decide), v4.other _ (by decide), v3.other _ (by decide), v2.other _ (by decide), x1]
  have s6 : (u6.gpr .r6).toNat = h + acc + (h + acc) * sv % 2 ^ 16 * s := by
    rw [v6.gpr, dpVal, BitVec.toNat_add, s5, x5]
    have : (h + acc) * sv % 2 ^ 16 * s < 2 ^ 16 * 8162 := Nat.mul_lt_mul'' hq hs.2
    omega_using [r5, hh, hacc, r4, hs, hinv, ha, x1, sv16, q4, hq, s5, x5, this]
  obtain ⟨_, hlt, hcong⟩ := redc16_math (X := h + acc) (s := s) (sv := sv) hinv (by
    have : 3 * 2 ^ 16 ≤ s * 2 ^ 16 := Nat.mul_le_mul_right _ hs.1
    omega_using [r5, hh, hacc, hs, hinv, ha, x1, q4, hq, s5, x5, s6, this])
  refine k u7 k7 m7 _ hlt hcong ?_
  apply BitVec.eq_of_toNat_eq
  rw [v7.gpr, hi16, s6, toNat_imm (by omega_arith)]

end VG.Proof.Bignum.Arm.TrialDivision16
