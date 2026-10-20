module

public import VerifiedGarbage.Impl.Ed448.Comb
public import VerifiedGarbage.Proof.X448.BaseTable

/-! The table and scalar arithmetic of the four-column, 456-bit fixed-base comb. -/

@[expose] public section

namespace VG.Proof.Ed448.Comb

set_option exponentiation.threshold 1024

open VG.Spec.Ed448 VG.Impl.Ed448.Comb VG.Proof.Ed448 VG.Proof.EdwardsLaw

private def checkEntry (i : Nat) : Bool :=
  let p := pointMul (weight i) basePoint
  let q := entry i
  q.1 * p.Z == p.X && q.2 * p.Z == p.Y

private theorem entries_check : ∀ i < 16, checkEntry i = true := by decide +kernel

/-- Every table entry represents the stated multiple, with nonzero projective `Z`. -/
theorem entry_rep (i : Nat) (hi : i < 16) :
    Rep (VG.Proof.X448.basePt (entry i)) ((weight i) • baseAff) := by
  have h := entries_check i hi
  simp only [checkEntry, Bool.and_eq_true, beq_iff_eq] at h
  exact VG.Proof.X448.basePt_rep (pointMul_rep _ basePoint_rep) h.1 h.2

/-- The four scalar bits consumed by iteration `t`, encoded as an index. -/
def digit (k t : Nat) : Nat :=
  (k / 2 ^ t) % 2 + (k / 2 ^ (t + 114)) % 2 * 2 +
  (k / 2 ^ (t + 228)) % 2 * 4 + (k / 2 ^ (t + 342)) % 2 * 8

theorem digit_lt (k t : Nat) : digit k t < 16 := by
  unfold digit
  omega

/-- The represented scalar after processing all column bits above `n - 1`. -/
def accScalar (k n : Nat) : Nat :=
  (k % 2 ^ 114) / 2 ^ n + (k / 2 ^ 114 % 2 ^ 114) / 2 ^ n * 2 ^ 114 +
  (k / 2 ^ 228 % 2 ^ 114) / 2 ^ n * 2 ^ 228 +
  (k / 2 ^ 342 % 2 ^ 114) / 2 ^ n * 2 ^ 342

theorem accScalar_start (k : Nat) : accScalar k 114 = 0 := by
  simp only [accScalar, Nat.mod_div_self, Nat.zero_mul, Nat.zero_add]

private theorem limb_bit (k b t : Nat) (ht : t < 114) :
    (k / 2 ^ b % 2 ^ 114) / 2 ^ t % 2 = k / 2 ^ (t + b) % 2 := by
  have hpow : 2 ^ 114 = 2 ^ t * (2 * 2 ^ (113 - t)) := by
    rw [← Nat.pow_succ', ← Nat.pow_add]
    congr 1; omega
  rw [hpow, Nat.mod_mul_right_div_self, Nat.mod_mul_right_mod,
    Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.add_comm b t]

private theorem limb_step (k b t : Nat) (ht : t < 114) :
    (k / 2 ^ b % 2 ^ 114) / 2 ^ t =
      2 * ((k / 2 ^ b % 2 ^ 114) / 2 ^ (t + 1)) + k / 2 ^ (t + b) % 2 := by
  have hd : (k / 2 ^ b % 2 ^ 114) / 2 ^ (t + 1) =
      ((k / 2 ^ b % 2 ^ 114) / 2 ^ t) / 2 := by
    rw [Nat.pow_succ 2 t, Nat.div_div_eq_div_mul]
  rw [hd, ← limb_bit k b t ht]
  omega

private theorem weight_bits : ∀ a < 2, ∀ b < 2, ∀ c < 2, ∀ d < 2,
    weight (a + b * 2 + c * 4 + d * 8) =
      a + b * 2 ^ 114 + c * 2 ^ 228 + d * 2 ^ 342 := by decide +kernel

theorem accScalar_step (k t : Nat) (ht : t < 114) :
    accScalar k t = 2 * accScalar k (t + 1) + weight (digit k t) := by
  have h0 := limb_step k 0 t ht
  have h1 := limb_step k 114 t ht
  have h2 := limb_step k 228 t ht
  have h3 := limb_step k 342 t ht
  simp only [Nat.pow_zero, Nat.div_one, Nat.add_zero] at h0
  rw [digit, weight_bits _ (Nat.mod_lt _ (by decide)) _ (Nat.mod_lt _ (by decide))
    _ (Nat.mod_lt _ (by decide)) _ (Nat.mod_lt _ (by decide)), accScalar, h0, h1, h2, h3, accScalar]
  ring

theorem accScalar_total (k : Nat) (hk : k < 2 ^ 456) : accScalar k 0 = k := by
  simp only [accScalar, Nat.pow_zero, Nat.div_one]
  have h1 := Nat.mod_add_div k (2 ^ 114)
  have h2 := Nat.mod_add_div (k / 2 ^ 114) (2 ^ 114)
  have h3 := Nat.mod_add_div (k / 2 ^ 228) (2 ^ 114)
  have h4 : k / 2 ^ 342 < 2 ^ 114 := (Nat.div_lt_iff_lt_mul (by decide)).mpr (by
    rw [← Nat.pow_add]; exact hk)
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add] at h2 h3
  rw [Nat.mod_eq_of_lt h4]
  omega

end VG.Proof.Ed448.Comb
