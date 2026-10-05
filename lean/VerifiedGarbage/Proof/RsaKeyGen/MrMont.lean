import VerifiedGarbage.Proof.RsaKeyGen.CandSpec
import VerifiedGarbage.Proof.Bignum.Math

/-!
# Miller–Rabin in Montgomery form

The implementations keep `y` as `y R mod c` (`R = 2^(64 w)`): a Montgomery
multiplication of `x R mod c` and `z R mod c` is `(x z mod c) R mod c`
(`mont_val`); `y R mod c` is `R mod c` iff `y = 1` and `c − R mod c` iff
`y = c − 1` (`mont_eq_one`, `mont_eq_m1`). They run the flag over the bits of
`c − 1` from the top: `mrPre c b T j P` after `j` of the `T` bits, which
after `T − 1` of them is `mrRun` (`mrRun_pre`), and `y` after `j` bits is
`mrPow c b T j` (`mrPow_succ`).
-/

namespace VG.Proof.RsaKeyGen

open VG.Spec.RsaKeyGen VG.Spec.Rsa

/-- A Montgomery multiplication in canonical form. -/
theorem mont_val {c R O A B x z : Nat} (hR : Nat.Coprime R c) (hO : O < c) (h : O * R % c = A * B % c)
    (hA : A = x * R % c) (hB : B = z * R % c) : O = x * z % c * R % c := by
  rw [← Nat.mod_eq_of_lt hO]
  apply VG.Proof.Bignum.mont_cancel hR
  rw [h, hA, hB, ← Nat.mul_mod, Nat.mul_assoc (x * z % c), Nat.mod_mul_mod]
  congr 1
  simp only [Nat.mul_assoc, Nat.mul_left_comm]

theorem mont_inj {c R x y : Nat} (hR : Nat.Coprime R c) (hx : x < c) (hy : y < c)
    (h : x * R % c = y * R % c) : x = y := by
  have := VG.Proof.Bignum.mont_cancel hR h
  rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this

theorem mont_eq_one {c R y : Nat} (hR : Nat.Coprime R c) (hc : 1 < c) (hy : y < c) :
    (y * R % c = R % c) ↔ y = 1 := by
  constructor
  · intro h
    exact mont_inj hR hy hc (by rw [h, Nat.one_mul])
  · rintro rfl; rw [Nat.one_mul]

theorem mont_m1 {c R : Nat} (hR : Nat.Coprime R c) (hc : 1 < c) : (c - 1) * R % c = c - R % c := by
  have hr : 0 < R % c := by
    rcases Nat.eq_zero_or_pos (R % c) with h | h
    · exfalso
      have h1 : Nat.gcd R c = c := Nat.gcd_eq_right (Nat.dvd_of_mod_eq_zero h)
      rw [Nat.Coprime] at hR; omega
    · exact h
  have hlt := Nat.mod_lt R (show 0 < c by omega)
  have e : (c - 1) * R + R % c = c * R - (R - R % c) := by
    rw [Nat.sub_mul, Nat.one_mul]
    have := Nat.mod_le R c
    have : R ≤ c * R := Nat.le_mul_of_pos_left R (by omega)
    omega
  have hd : c ∣ R - R % c := Nat.dvd_sub_mod R
  obtain ⟨q, hq⟩ := hd
  have hqR : q ≤ R := by
    have := Nat.sub_le R (R % c)
    rw [hq] at this
    exact Nat.le_trans (Nat.le_mul_of_pos_left q (by omega)) this
  have e2 : (c - 1) * R + R % c = c * (R - q) := by rw [e, hq, Nat.mul_sub]
  have : ((c - 1) * R + R % c) % c = 0 := by rw [e2, Nat.mul_mod_right]
  have h3 : ((c - 1) * R % c + R % c) % c = 0 := by rw [Nat.add_mod, Nat.mod_mod] at this; exact this
  have h4 := Nat.mod_lt ((c - 1) * R) (show 0 < c by omega)
  have h5 : (c - 1) * R % c + R % c = c := by
    rcases Nat.lt_or_ge ((c - 1) * R % c + R % c) c with h | h
    · rw [Nat.mod_eq_of_lt h] at h3; omega
    · have : (c - 1) * R % c + R % c - c < c := by omega
      have e3 := Nat.mod_eq_sub_mod h
      rw [Nat.mod_eq_of_lt this] at e3; omega
  omega

theorem mont_eq_m1 {c R y : Nat} (hR : Nat.Coprime R c) (hc : 1 < c) (hy : y < c) :
    (y * R % c = c - R % c) ↔ y = c - 1 := by
  rw [← mont_m1 hR hc]
  exact ⟨fun h => mont_inj hR hy (by omega) h, fun h => by rw [h]⟩

/-- The flag after the `j` top bits of the `T` bits of `c − 1`. -/
def mrPre (c b T : Nat) : Nat → Bool → Bool
  | 0, P => P
  | j + 1, P => mrFlag c b (T - 1 - j) (mrPre c b T j P)

theorem mrRun_pre_gen (c b T : Nat) (P : Bool) : ∀ k j, j + k = T - 1 →
    mrRun c b k (mrPre c b T j P) = mrPre c b T (j + k) P
  | 0, j, _ => rfl
  | k + 1, j, h => by
    rw [mrRun, show mrFlag c b (k + 1) (mrPre c b T j P) = mrPre c b T (j + 1) P by
      rw [mrPre, show T - 1 - j = k + 1 by omega], mrRun_pre_gen c b T P k (j + 1) (by omega)]
    congr 1; omega

theorem mrRun_pre (c b T : Nat) (P : Bool) : mrRun c b (T - 1) P = mrPre c b T (T - 1) P := by
  have := mrRun_pre_gen c b T P (T - 1) 0 (by omega)
  rwa [Nat.zero_add] at this

/-- `y` after the `j` top bits of the `T` bits of `c − 1`. -/
def mrPow (c b T j : Nat) : Nat := powMod b ((c - 1) / 2 ^ (T - j)) c

theorem powMod_step (b e c d : Nat) (hd : d < 2) :
    powMod b (2 * e + d) c = (powMod b e c * powMod b e c % c) * (if d = 1 then b else 1) % c := by
  rcases Nat.eq_zero_or_pos e with rfl | he
  · rcases (by omega : d = 0 ∨ d = 1) with rfl | rfl
    · simp only [Nat.mul_zero, Nat.add_zero]
      rw [powMod]; simp
    · simp only [Nat.mul_zero, Nat.zero_add, ↓reduceIte]
      rw [powMod]
      simp only [show (1 : Nat) ≠ 0 by omega, ↓reduceIte]
  · rw [powMod]
    simp only [show 2 * e + d ≠ 0 by omega, ↓reduceIte, show (2 * e + d) / 2 = e by omega,
      show (2 * e + d) % 2 = d by omega]
    rcases (by omega : d = 0 ∨ d = 1) with rfl | rfl
    · simp
    · simp

theorem mrPow_succ (c b T j : Nat) (hj : j < T) :
    mrPow c b T (j + 1) = (mrPow c b T j * mrPow c b T j % c) *
      (if (c - 1) / 2 ^ (T - 1 - j) % 2 = 1 then b else 1) % c := by
  unfold mrPow
  have e : (c - 1) / 2 ^ (T - (j + 1)) = 2 * ((c - 1) / 2 ^ (T - j)) + (c - 1) / 2 ^ (T - 1 - j) % 2 := by
    rw [show T - j = (T - 1 - j) + 1 by omega, show T - (j + 1) = T - 1 - j by omega, Nat.pow_succ,
      ← Nat.div_div_eq_div_mul]
    omega
  rw [e, powMod_step _ _ _ _ (Nat.mod_lt _ (by decide))]

theorem mrPow_zero {c b T : Nat} (hT : c - 1 < 2 ^ T) (hc : 1 < c) : mrPow c b T 0 = 1 := by
  unfold mrPow
  rw [Nat.sub_zero, Nat.div_eq_of_lt hT, powMod]; simp only [↓reduceIte]; exact Nat.mod_eq_of_lt hc

theorem mrPre_succ (c b T j : Nat) (P : Bool) (hj : j < T) :
    mrPre c b T (j + 1) P =
      if (c - 1) / 2 ^ (T - 1 - j) % 2 = 1 then (mrPow c b T (j + 1) == 1 || mrPow c b T (j + 1) == c - 1)
      else (mrPre c b T j P || mrPow c b T (j + 1) == c - 1) := by
  rw [mrPre, mrFlag]
  unfold mrPow
  rw [show T - (j + 1) = T - 1 - j by omega]

theorem beq_dec (a b : Nat) : (a == b) = decide (a = b) := by
  by_cases h : a = b <;> simp [h]

/-- One bit of the exponentiation, for the bit `bt` of `c − 1` at `T − 1 − j`. -/
theorem mr_step {c b T j : Nat} (P : Bool) {bt : Bool} (hj : j < T)
    (hcond : ((c - 1) / 2 ^ (T - 1 - j) % 2 = 1) ↔ bt = true) :
    mrPow c b T (j + 1) = mrPow c b T j * mrPow c b T j % c * (if bt then b else 1) % c ∧
    mrPre c b T (j + 1) P = if bt then decide (mrPow c b T (j + 1) = 1) || decide (mrPow c b T (j + 1) = c - 1)
      else mrPre c b T j P || decide (mrPow c b T (j + 1) = c - 1) := by
  have e : ((c - 1) / 2 ^ (T - 1 - j) % 2 = 1) = (bt = true) := propext hcond
  refine ⟨?_, ?_⟩
  · rw [mrPow_succ c b T j hj]; simp only [e]
  · rw [mrPre_succ c b T j P hj]; simp only [e, beq_dec]

/-- The bits of an odd `c` and of `c − 1` agree but for bit 0. -/
theorem odd_sub_one_div {c i : Nat} (hc : c % 2 = 1) (hi : 1 ≤ i) : (c - 1) / 2 ^ i = c / 2 ^ i := by
  obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  rw [Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
    show (c - 1) / 2 = c / 2 by omega]

theorem div_bit_iff (c i : Nat) : (c / 2 ^ i % 2 = 1) ↔ c.testBit i = true := by
  rw [Nat.testBit_eq_decide_div_mod_eq]; simp

/-- The top bit of `x` shifted left by `t ≤ 63`: bit `63 − t` of `x`. -/
theorem shl_shr63 (x : BitVec 64) {t : Nat} (ht : t ≤ 63) :
    (x <<< t) >>> 63 = BitVec.ofNat 64 (x.toNat.testBit (63 - t)).toNat := by
  apply BitVec.eq_of_toNat_eq
  have e1 : x.toNat * 2 ^ t % 2 ^ 64 / 2 ^ 63 = x.toNat * 2 ^ t / 2 ^ 63 % 2 := by
    rw [show (2 : Nat) ^ 64 = 2 ^ 63 * 2 from rfl, Nat.mod_mul_right_div_self]
  have e2 : x.toNat * 2 ^ t / 2 ^ 63 = x.toNat / 2 ^ (63 - t) := by
    rw [show (2 : Nat) ^ 63 = 2 ^ t * 2 ^ (63 - t) by rw [← Nat.pow_add]; congr 1; omega,
      ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel _ (Nat.two_pow_pos t)]
  have hb : (x.toNat.testBit (63 - t)).toNat < 2 ^ 64 := by cases x.toNat.testBit (63 - t) <;> decide
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow, e1, e2, Nat.mod_eq_of_lt hb, Nat.testBit_eq_decide_div_mod_eq]
  have := Nat.mod_lt (x.toNat / 2 ^ (63 - t)) (show 0 < 2 by decide)
  rcases (by omega : x.toNat / 2 ^ (63 - t) % 2 = 0 ∨ x.toNat / 2 ^ (63 - t) % 2 = 1) with h | h <;> simp [h]

end VG.Proof.RsaKeyGen
