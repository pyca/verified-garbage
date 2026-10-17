module

public import VerifiedGarbage.Proof.RsaKeyGen.MrMont
public import VerifiedGarbage.Spec.MillerRabin
import VerifiedGarbage.Proof.Bignum.Math
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# The Miller–Rabin round on ARMv7: the arithmetic

The round runs binary exponentiation over the bits `64 w − 1` down to 1 of
`c − 1` (those of `c`, `ebit`), in Montgomery form: a product of `x` and
`y` is `mm c w x y = x y R⁻¹ mod c`, with `R⁻¹ = ((c + 1) / 2)^(64 w) mod
c` the inverse of `R = 2^(64 w)` (`mm_eq`). `yseq` and `fseq` are the
values `y` and the flag it computes from the witness `X`, Montgomery one `O`
and minus one `M`; for any `b` with `X = b R mod c`, they are those of
`mrPow` and `mrPre` (`seq_spec`), and the flag after the last bit is the
round's result (`fseq_round`). A copy of `c` shifted left one bit a step
gives the bits (`shift_carry`, `shift_val`).
-/

@[expose] public section

namespace VG.Proof.MillerRabin.Arm
open VG.Spec.RsaKeyGen VG.Spec.Rsa VG.Proof.RsaKeyGen

/-! ## Montgomery products -/

/-- The inverse of `2^(64 w)` modulo the odd `c`. -/
def rinv (c w : Nat) : Nat := ((c + 1) / 2) ^ (64 * w) % c

/-- `x y R⁻¹ mod c`. -/
def mm (c w x y : Nat) : Nat := x * y * rinv c w % c

theorem R_rinv {c w : Nat} (hc : c % 2 = 1) : 2 ^ (64 * w) * rinv c w % c = 1 % c := by
  unfold rinv
  rw [Nat.mul_mod_mod, ← Nat.mul_pow, Nat.pow_mod, show 2 * ((c + 1) / 2) = c + 1 by omega,
    show (c + 1) % c = 1 % c by rw [Nat.add_mod_left], ← Nat.pow_mod, Nat.one_pow]

/-- The value of a Montgomery product. -/
theorem mm_eq {c w T x y : Nat} (hc : c % 2 = 1) (hT : T < c) (h : T * 2 ^ (64 * w) % c = x * y % c) :
    T = mm c w x y := by
  unfold mm
  have e : T % c = T * (2 ^ (64 * w) * rinv c w) % c := by
    rw [Nat.mul_mod, R_rinv hc, ← Nat.mul_mod, Nat.mul_one]
  rw [← Nat.mod_eq_of_lt hT, e, ← Nat.mul_assoc, Nat.mul_mod, h, ← Nat.mul_mod]

/-- The product of two Montgomery forms. -/
theorem mm_val {c w x z : Nat} (hc : c % 2 = 1) :
    mm c w (x * 2 ^ (64 * w) % c) (z * 2 ^ (64 * w) % c) = x * z % c * 2 ^ (64 * w) % c := by
  unfold mm
  generalize hR : 2 ^ (64 * w) = R
  have r := R_rinv (w := w) hc
  rw [hR] at r
  rw [Nat.mul_mod (x * R % c * (z * R % c)), ← Nat.mul_mod (x * R) (z * R), ← Nat.mul_mod,
    Nat.mul_mod (x * z % c) R, Nat.mod_mod, ← Nat.mul_mod,
    show x * R * (z * R) * rinv c w = x * z * R * (R * rinv c w) by
      simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm],
    Nat.mul_mod (x * z * R), r, ← Nat.mul_mod, Nat.mul_one]

/-! ## The bits -/

/-- Bit `64 w − 1 − j` of `c`. -/
def ebit (c w j : Nat) : Bool := c / 2 ^ (64 * w - 1 - j) % 2 == 1

/-- The carry of a left shift of `x 2^j mod 2^n` is bit `n − 1 − j` of `x`. -/
theorem shift_carry (x n j : Nat) (hj : j < n) : 2 * (x * 2 ^ j % 2 ^ n) / 2 ^ n = x / 2 ^ (n - 1 - j) % 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = j + k + 1 := ⟨n - j - 1, by omega⟩
  rw [show j + k + 1 - 1 - j = k by omega, show 2 ^ (j + k + 1) = 2 ^ (k + 1) * 2 ^ j by
      rw [← Nat.pow_add]; congr 1; omega, Nat.mul_mod_mul_right, ← Nat.mul_assoc, Nat.mul_comm 2,
    Nat.mul_div_mul_right _ _ (Nat.two_pow_pos j), Nat.pow_succ]
  have key : ∀ r, r * 2 / (2 ^ k * 2) = r / 2 ^ k := fun r =>
    Nat.mul_div_mul_right _ _ (by decide)
  rw [key, Nat.mod_mul_right_div_self]

theorem shift_val (x n j : Nat) : 2 * (x * 2 ^ j % 2 ^ n) % 2 ^ n = x * 2 ^ (j + 1) % 2 ^ n := by
  rw [Nat.mul_mod_mod, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm 2 x, Nat.mul_assoc x 2, Nat.mul_comm 2 (2 ^ j),
    ← Nat.mul_assoc]

/-! ## The sequences -/

/-- `y` after `j` bits, from the witness `X` and Montgomery one `O`. -/
def yseq (c w X O : Nat) : Nat → Nat
  | 0 => O
  | j + 1 => mm c w (mm c w (yseq c w X O j) (yseq c w X O j)) (if ebit c w j then X else O)

/-- The flag after `j` bits, with Montgomery minus one `M`. -/
def fseq (c w X O M : Nat) : Nat → Bool
  | 0 => false
  | j + 1 => if ebit c w j then (yseq c w X O (j + 1) == O || yseq c w X O (j + 1) == M)
      else (fseq c w X O M j || yseq c w X O (j + 1) == M)

theorem mrPow_lt {c b T j : Nat} (hc : 0 < c) : mrPow c b T j < c := by
  unfold mrPow; rw [VG.Proof.Bignum.powMod_eq]; exact Nat.mod_lt _ hc

theorem seq_spec {c w b X O M : Nat} (hc : c % 2 = 1) (hc3 : 3 ≤ c) (hcR : c < 2 ^ (64 * w))
    (hX : X = b % c * 2 ^ (64 * w) % c) (hO : O = 2 ^ (64 * w) % c) (hM : M = c - 2 ^ (64 * w) % c) :
    ∀ j, j < 64 * w → yseq c w X O j = mrPow c b (64 * w) j * 2 ^ (64 * w) % c ∧
      fseq c w X O M j = mrPre c b (64 * w) j false
  | 0, _ => by
    refine ⟨?_, rfl⟩
    rw [yseq, mrPow_zero (by omega) (by omega), Nat.one_mul, hO]
  | j + 1, hj => by
    obtain ⟨ihY, ihF⟩ := seq_spec hc hc3 hcR hX hO hM j (by omega)
    have hR : Nat.Coprime (2 ^ (64 * w)) c := VG.Proof.Bignum.coprime_pow2 hc _
    have hcond : ((c - 1) / 2 ^ (64 * w - 1 - j) % 2 = 1) ↔ ebit c w j = true := by
      rw [odd_sub_one_div hc (by omega)]; simp [ebit]
    obtain ⟨sY, sF⟩ := mr_step (c := c) (b := b) (T := 64 * w) (j := j) false (bt := ebit c w j) (by omega) hcond
    have yv : yseq c w X O (j + 1) = mrPow c b (64 * w) (j + 1) * 2 ^ (64 * w) % c := by
      rw [yseq, ihY, mm_val hc]
      have hm : (if ebit c w j = true then X else O) =
          (if ebit c w j = true then b % c else 1) * 2 ^ (64 * w) % c := by
        split
        · exact hX
        · rw [hO, Nat.one_mul]
      rw [hm, mm_val hc, sY]
      congr 1
      split
      · rw [Nat.mul_mod_mod]
      · rfl
    refine ⟨yv, ?_⟩
    have hlt := mrPow_lt (c := c) (b := b) (T := 64 * w) (j := j + 1) (by omega)
    have e1 : (yseq c w X O (j + 1) == O) = decide (mrPow c b (64 * w) (j + 1) = 1) := by
      rw [yv, hO, VG.Proof.RsaKeyGen.beq_dec]
      exact decide_eq_decide.mpr (mont_eq_one hR (by omega) hlt)
    have e2 : (yseq c w X O (j + 1) == M) = decide (mrPow c b (64 * w) (j + 1) = c - 1) := by
      rw [yv, hM, VG.Proof.RsaKeyGen.beq_dec]
      exact decide_eq_decide.mpr (mont_eq_m1 hR (by omega) hlt)
    rw [fseq, sF, e1, e2, ← ihF]

/-! ## The round -/

/-- `mrRun_eq` for any `T` with `c − 1 < 2^T`. -/
theorem mrRun_eq' {w b T : Nat} (hw : 3 ≤ w) (hw2 : w % 2 = 1) (hT : w - 1 < 2 ^ T) (P : Bool) :
    mrRun w b (T - 1) P =
      mrIteration w (splitTwos (w - 1)).1 (splitTwos (w - 1)).2 b := by
  apply Bool.eq_iff_iff.mpr
  obtain ⟨hN, hm2⟩ := splitTwos_spec (w - 1) (by omega)
  generalize (splitTwos (w - 1)).1 = a at hN hm2 ⊢
  generalize (splitTwos (w - 1)).2 = m at hN hm2 ⊢
  have hm : 0 < m := by omega
  have ha : 1 ≤ a := by
    rcases a with _ | a
    · rw [Nat.pow_zero, Nat.mul_one] at hN; omega
    · omega
  have h2a : 2 ^ a ≤ w - 1 := by rw [hN]; exact Nat.le_mul_of_pos_left _ hm
  have haT : a < T := by
    rcases Nat.lt_or_ge a T with h | h
    · exact h
    exfalso
    have : 2 ^ T ≤ 2 ^ a := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have haw : a ≤ bitLength w - 1 := by
    have e : bitLength w = w.log2 + 1 := by unfold bitLength; split <;> omega
    rw [e, Nat.add_sub_cancel]
    exact (Nat.le_log2 (by omega)).mpr (by omega)
  rw [mrRun_high w b m a hm hm2 hN ha (T - 1) (by omega) P, mrRun_low w b m a hm hN (a - 1) (by omega),
    mrIteration_iff hw ha haw]
  have hdiv : (w - 1) / 2 ^ a = m := by rw [hN, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
  unfold mrFlag
  simp only [hdiv, hm2, ↓reduceIte]
  simp only [Bool.or_eq_true, beq_iff_eq]
  constructor
  · rintro ((h | h) | ⟨i, h1, h2, he⟩)
    · exact .inl h
    · exact .inr ⟨0, by omega, h⟩
    · exact .inr ⟨a - i, by omega, he⟩
  · rintro (h | ⟨t, ht, he⟩)
    · exact .inl (.inl h)
    · rcases t with _ | t
      · exact .inl (.inr he)
      · exact .inr ⟨a - (t + 1), by omega, by omega, by rw [show a - (a - (t + 1)) = t + 1 by omega]; exact he⟩

/-- After the last bit, the flag is the round's result. -/
theorem fseq_round {c w b X O M : Nat} (hc : c % 2 = 1) (hc3 : 3 ≤ c) (hcR : c < 2 ^ (64 * w)) (hw : 1 ≤ w)
    (hX : X = b % c * 2 ^ (64 * w) % c) (hO : O = 2 ^ (64 * w) % c) (hM : M = c - 2 ^ (64 * w) % c) :
    fseq c w X O M (64 * w - 1) = Spec.MillerRabin.round c b := by
  rw [(seq_spec hc hc3 hcR hX hO hM (64 * w - 1) (by omega)).2, ← mrRun_pre, mrRun_eq' hc3 hc (by omega)]
  rfl

end VG.Proof.MillerRabin.Arm
