module

public import VerifiedGarbage.Proof.Rsa.X86.Rd.SqrtWBase
public import VerifiedGarbage.Proof.Bignum.SqrtRem
public import VerifiedGarbage.Proof.Bignum.WordStep32
import VerifiedGarbage.Proof.Bignum.WordStepNorm32
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Rsa.X86.Rd.SqrtWWin
import VerifiedGarbage.Proof.Rsa.X86.Rd.Loops
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Scalar
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.X86.ExponentWord
import VerifiedGarbage.Proof.Bignum.X86.R2Words.Quot
import VerifiedGarbage.Proof.Bignum.WordTop32
import VerifiedGarbage.Proof.Rsa.X86.Rd.SqrtWFix
import VerifiedGarbage.Proof.Rsa.X86.Rd.SqrtWSub
import VerifiedGarbage.Proof.Rsa.X86.Rd.Move
import VerifiedGarbage.Proof.Rsa.X86.WordRt.Loop

-- separate module: the digit step, its own proof, which `SqrtW` and the timing import

/-! # The square root by words on i686: a digit step

`stepX`, with `j` digits left (`sCt`) and `m = j - 1`: the 3-by-2 estimate `q̂` of
`⌊R / (2 s β)⌋` (`R = r β² + P`, `β = 2^32`) from the top three words of `⌊R / 2⌋` and the
top two of `s β` (`estX`, `R2Words.quot` and `refine3`), `T = R - (2 s β + q̂) q̂`
(`mulSubX`), three masked corrections (`fixX`, `SqrtRem.correction_step`), `D := 2 s' β^m`
(`toE`, `updX`) and `T` back in place of `R` (`copyBackX`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.Recover

open VG.Proof.Bignum.SqrtRem (IsDigit)

/-! ## The arithmetic -/

/-- Word `i` of `x`. -/
abbrev wd (x i : Nat) : Nat := x / 2 ^ (32 * i) % 2 ^ 32

/-- A word of `⌊x / 2⌋` from two words of `x`. -/
theorem half_wd (x i : Nat) : wd (x / 2) i = wd x (i + 1) % 2 * 2 ^ 31 + wd x i / 2 := by
  have e1 : x / 2 / 2 ^ (32 * i) = x / 2 ^ (32 * i) / 2 := by
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm]
  have e2 : x / 2 ^ (32 * (i + 1)) = x / 2 ^ (32 * i) / 2 ^ 32 := by
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.mul_add, Nat.mul_one]
  simp only [wd]
  rw [e1, e2]
  generalize x / 2 ^ (32 * i) = y
  omega_using []

/-- The quotient of truncations is at least the quotient. -/
theorem div_le_trunc {Y N K : Nat} (hD : 0 < N / 2 ^ K) : Y / N ≤ Y / 2 ^ K / (N / 2 ^ K) := by
  rw [Nat.le_div_iff_mul_le hD, Nat.le_div_iff_mul_le (Nat.two_pow_pos _)]
  have h1 : N / 2 ^ K * 2 ^ K ≤ N := Nat.div_mul_le_self N _
  have h2 : Y / N * N ≤ Y := Nat.div_mul_le_self Y N
  calc Y / N * (N / 2 ^ K) * 2 ^ K = Y / N * (N / 2 ^ K * 2 ^ K) := by rw [Nat.mul_assoc]
    _ ≤ Y / N * N := Nat.mul_le_mul_left _ h1
    _ ≤ Y := h2

/-- The top two words of a normalized `s β` (`s` of `k + 1` words, its top one at least `2^31`). -/
theorem top2_bounds {s k : Nat} (hs1 : 2 ^ 31 * 2 ^ (32 * k) ≤ s) (hs2 : s < 2 ^ (32 * (k + 1))) :
    2 ^ 63 ≤ s * 2 ^ 32 / 2 ^ (32 * k) ∧ s * 2 ^ 32 / 2 ^ (32 * k) < 2 ^ 64 := by
  have hG := Nat.two_pow_pos (32 * k)
  have e : 2 ^ (32 * (k + 1)) = 2 ^ (32 * k) * 2 ^ 32 := by rw [Nat.mul_add, Nat.pow_add]
  constructor
  · rw [Nat.le_div_iff_mul_le hG]
    have := Nat.mul_le_mul_right (2 ^ 32) hs1
    calc 2 ^ 63 * 2 ^ (32 * k) = 2 ^ 31 * 2 ^ (32 * k) * 2 ^ 32 := by
          rw [Nat.mul_right_comm, show (2 : Nat) ^ 63 = 2 ^ 31 * 2 ^ 32 from rfl]
      _ ≤ s * 2 ^ 32 := this
  · rw [Nat.div_lt_iff_lt_mul hG]
    have := Nat.mul_lt_mul_of_pos_right hs2 (show 0 < 2 ^ 32 by decide)
    rw [e] at this
    calc s * 2 ^ 32 < 2 ^ (32 * k) * 2 ^ 32 * 2 ^ 32 := this
      _ = 2 ^ 64 * 2 ^ (32 * k) := by
          rw [Nat.mul_assoc, Nat.mul_comm, show (2 : Nat) ^ 32 * 2 ^ 32 = 2 ^ 64 from rfl]

/-- `⌊R / 2⌋`'s top words against `s β`'s, for `s` of `k + 2` words (`β G`, `G = 2^(32 k)`)
and `r ≤ 2 s`: `U < (D + 1) β`. -/
theorem est_top {s r P k : Nat} (hr : r ≤ 2 * s) (hP : P < 2 ^ 64) :
    (r * 2 ^ 64 + P) / 2 / (2 ^ 32 * 2 ^ (32 * k)) < (s / 2 ^ (32 * k) + 1) * 2 ^ 32 := by
  obtain ⟨G, eG⟩ : ∃ G, 2 ^ (32 * k) = G := ⟨_, rfl⟩
  have hG : 0 < G := eG ▸ Nat.two_pow_pos (32 * k)
  rw [eG]
  have hs : s + 1 ≤ (s / G + 1) * G := VG.Proof.Bignum.WordStep32.lt_succ_div_mul s G hG
  obtain ⟨D, eD⟩ : ∃ D, s / G = D := ⟨_, rfl⟩
  rw [eD] at hs ⊢
  rw [Nat.div_lt_iff_lt_mul (Nat.mul_pos (by decide) hG)]
  have h1 : (s + 1) * 2 ^ 64 ≤ (D + 1) * G * 2 ^ 64 := Nat.mul_le_mul_right _ hs
  have e : (D + 1) * 2 ^ 32 * (2 ^ 32 * G) = (D + 1) * G * 2 ^ 64 := by
    rw [show (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 by rw [← Nat.pow_add]]
    ac_rfl
  rw [e]
  obtain ⟨M, eM⟩ : ∃ M, (D + 1) * G = M := ⟨_, rfl⟩
  rw [eM] at h1 ⊢
  omega_using [hr, hP, h1]

/-- The estimate of a digit, for `s` of `k + 1` words, its top one at least `2^31`, `r ≤ 2 s`,
`R = r β² + P`, `U = ⌊⌊R / 2⌋ / 2^(32 k)⌋` (three words) and `D = ⌊s β / 2^(32 k)⌋` (two):
`U < (β + 1) D`, `U`'s top word at most `D`'s, and `Q = min(⌊U / D⌋, β - 1)` within two above
the digit `q`. -/
theorem est_bounds {s r P k : Nat} (hs1 : 2 ^ 31 * 2 ^ (32 * k) ≤ s) (hs2 : s < 2 ^ (32 * (k + 1)))
    (hr : r ≤ 2 * s) (hP : P < 2 ^ 64) :
    (r * 2 ^ 64 + P) / 2 / 2 ^ (32 * k) < (2 ^ 32 + 1) * (s * 2 ^ 32 / 2 ^ (32 * k)) ∧
    (r * 2 ^ 64 + P) / 2 / 2 ^ (32 * k) / 2 ^ 64 ≤ s * 2 ^ 32 / 2 ^ (32 * k) / 2 ^ 32 ∧
    (r * 2 ^ 64 + P) / 2 / 2 ^ (32 * k) < 2 ^ 96 ∧
    ∀ q, IsDigit (2 ^ 32) s (r * 2 ^ 64 + P) q →
      q ≤ min ((r * 2 ^ 64 + P) / 2 / 2 ^ (32 * k) / (s * 2 ^ 32 / 2 ^ (32 * k))) (2 ^ 32 - 1) ∧
      min ((r * 2 ^ 64 + P) / 2 / 2 ^ (32 * k) / (s * 2 ^ 32 / 2 ^ (32 * k))) (2 ^ 32 - 1) ≤ q + 2 := by
  obtain ⟨d1, d2⟩ := top2_bounds hs1 hs2
  have hs0 : 2 ^ 31 ≤ s := Nat.le_trans (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)) hs1
  -- `U < (D + 1) β` (`k > 0`), `U < D β + β² / 2` (`k = 0`).
  have hUD : (r * 2 ^ 64 + P) / 2 / 2 ^ (32 * k) < (2 ^ 32 + 1) * (s * 2 ^ 32 / 2 ^ (32 * k)) ∧
      (r * 2 ^ 64 + P) / 2 / 2 ^ (32 * k) / 2 ^ 64 ≤ s * 2 ^ 32 / 2 ^ (32 * k) / 2 ^ 32 := by
    rcases k with _ | k
    · rw [Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.div_one] at *
      rw [Nat.mul_div_cancel _ (by decide)]
      constructor
      · rw [Nat.add_mul, Nat.one_mul]; omega_using [hr, hP, hs0]
      · rw [Nat.div_le_iff_le_mul_add_pred (by decide)]; omega_using [hr, hP]
    · have ht := est_top (k := k) hr hP
      have eG : 2 ^ (32 * (k + 1)) = 2 ^ 32 * 2 ^ (32 * k) := by rw [Nat.mul_add, Nat.pow_add, Nat.mul_comm]
      have eD : s * 2 ^ 32 / 2 ^ (32 * (k + 1)) = s / 2 ^ (32 * k) := by
        rw [eG, Nat.mul_comm s, Nat.mul_div_mul_left _ _ (by decide)]
      rw [eD] at d1 ⊢
      rw [eG]
      obtain ⟨U, eU⟩ : ∃ U, (r * 2 ^ 64 + P) / 2 / (2 ^ 32 * 2 ^ (32 * k)) = U := ⟨_, rfl⟩
      obtain ⟨D, eD⟩ : ∃ D, s / 2 ^ (32 * k) = D := ⟨_, rfl⟩
      rw [eU, eD] at ht
      rw [eD] at d1
      rw [eU, eD]
      rw [Nat.add_mul, Nat.one_mul] at ht
      constructor
      · rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (2 ^ 32)]; omega_using [d1, ht]
      · have : U / 2 ^ 32 ≤ D := by rw [Nat.div_le_iff_le_mul_add_pred (by decide)]; omega_using [ht]
        rw [show (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 by rw [← Nat.pow_add], ← Nat.div_div_eq_div_mul]
        exact Nat.div_le_div_right this
  obtain ⟨D, hD⟩ : ∃ D, s * 2 ^ 32 / 2 ^ (32 * k) = D := ⟨_, rfl⟩
  rw [hD] at d1 d2 hUD ⊢
  have hU2 := hUD.2
  refine ⟨hUD.1, hU2, by omega_using [hUD, d2], ?_⟩
  intro q hq
  have eb : (2 : Nat) ^ 32 * 2 ^ 32 = 2 ^ 64 := by rw [← Nat.pow_add]
  have hd : 0 < 2 * s * 2 ^ 32 := by omega_using [hs0]
  have hqβ : q < 2 ^ 32 := VG.Proof.Bignum.SqrtRem.digit_lt hr (by rw [eb]; exact hP) (by rw [eb]; exact hq.1)
  have hle := VG.Proof.Bignum.SqrtRem.digit_le_div hd hq.1
  have hge := VG.Proof.Bignum.SqrtRem.div_le_digit_succ (by omega_using [hs0]) hd hqβ hq.2
  have eR : (r * 2 ^ 64 + P) / (2 * s * 2 ^ 32) = (r * 2 ^ 64 + P) / 2 / (s * 2 ^ 32) := by
    rw [Nat.div_div_eq_div_mul, Nat.mul_assoc]
  rw [eR] at hle hge
  have tr := div_le_trunc (Y := (r * 2 ^ 64 + P) / 2) (N := s * 2 ^ 32) (K := 32 * k) (by rw [hD]; omega_using [d1])
  rw [hD] at tr
  obtain ⟨Y, eY⟩ : ∃ Y, (r * 2 ^ 64 + P) / 2 = Y := ⟨_, rfl⟩
  rw [eY] at hle hge tr ⊢
  rcases Nat.lt_or_ge (Y / (s * 2 ^ 32)) (2 ^ 32) with hlt | hlt
  · have := VG.Proof.Bignum.WordStep32.qhat_trunc (Y := Y) (N := s * 2 ^ 32) (K := 32 * k) hlt (by rw [hD]; omega_using [d1])
    rw [hD] at this
    exact ⟨Nat.le_trans hle this.1, by omega_arith⟩
  · refine ⟨Nat.le_min.mpr ⟨by omega_using [tr, hle], by omega_arith⟩, Nat.le_trans (Nat.min_le_right _ _) (by omega_arith)⟩

open VG.Proof.Bignum.WordStep32 (twos twos_eq twos_neg twos_of_add addIfNeg)

/-- `R - (S + q') q'` for `q ≤ q'` and the digit `q`: negative exactly where `q < q'`, and then
`S + 2 q' - 1` added is `R - (S + q' - 1) (q' - 1)` (`SqrtRem.correction_step`). -/
theorem fix_val {S R q q' : Nat} (hq : (S + q) * q ≤ R ∧ R < (S + (q + 1)) * (q + 1)) (hqq : q ≤ q') :
    ((R : Int) - ((S + q') * q' : Nat) < 0 ↔ q < q') ∧
      (q < q' → (R : Int) - ((S + q') * q' : Nat) + ((S + 2 * q' - 1 : Nat) : Int) =
        (R : Int) - ((S + (q' - 1)) * (q' - 1) : Nat)) := by
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun h => ?_⟩
  · rcases Nat.eq_or_lt_of_le hqq with rfl | hlt
    · exfalso; have := hq.1; omega_using [hq, h]
    · exact hlt
  · have : (S + (q + 1)) * (q + 1) ≤ (S + q') * q' := Nat.mul_le_mul (by omega_using [h]) h
    have := hq.2; omega_arith
  · have e := VG.Proof.Bignum.SqrtRem.correction_step S q' (by omega_using [h])
    rw [e]; push_cast; omega_using []

/-- The remainder through a correction, in two's complement modulo `W`: from
`T = twos W (R - (S + q') q')`, `T'` with `T' + W c = T + E` where `T` is negative (`E` is
`S + 2 q' - 1` for `q' ≥ 1`), is `twos W (R - (S + q'') q'')` for `q''` the estimate less one
where it was above the digit `q`. -/
theorem fix_step {W S R q q' T T' c E : Nat} (hq : (S + q) * q ≤ R ∧ R < (S + (q + 1)) * (q + 1))
    (hqq : q ≤ q') (hq2 : q' ≤ q + 2) (hW : R + 2 * S + 4 * q + 4 < W / 2)
    (hT : T = twos W ((R : Int) - ((S + q') * q' : Nat))) (hT' : T' < W) (hc : c < 2)
    (hE : 1 ≤ q' → E = S + 2 * q' - 1) (h : T' + W * c = T + if W / 2 ≤ T then E else 0) :
    (W / 2 ≤ T ↔ q < q') ∧ T' = twos W ((R : Int) - ((S + if q < q' then q' - 1 else q') *
      (if q < q' then q' - 1 else q') : Nat)) := by
  obtain ⟨hneg, hadd⟩ := fix_val hq hqq
  have hlo : (S + q) * q ≤ R := hq.1
  have hb : (S + q') * q' ≤ (S + q + 2) * (q + 2) := Nat.mul_le_mul (by omega_using [hq2]) hq2
  have e2 : (S + q + 2) * (q + 2) = (S + q) * q + (2 * S + 4 * q + 4) := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.add_mul]; omega_using []
  have b1 : -((W : Int) / 2) ≤ (R : Int) - ((S + q') * q' : Nat) := by
    have : ((W / 2 : Nat) : Int) = (W : Int) / 2 := by push_cast; rfl
    omega_using [hq, hqq, hq2, hW, hT', hE, h, hneg, hadd, hlo, hb, e2, this]
  have b2 : (R : Int) - ((S + q') * q' : Nat) < (W : Int) / 2 := by
    have : ((W / 2 : Nat) : Int) = (W : Int) / 2 := by push_cast; rfl
    omega_using [hq, hqq, hq2, hW, hT', hE, h, hneg, hadd, hlo, hb, e2, b1, this]
  have hn : W / 2 ≤ T ↔ q < q' := by rw [hT, twos_neg b1 b2]; exact hneg
  refine ⟨hn, ?_⟩
  by_cases hlt : q < q'
  · simp only [hlt, ite_true]
    have hb' : (S + (q' - 1)) * (q' - 1) ≤ (S + q + 1) * (q + 1) := Nat.mul_le_mul (by omega_using [hq, hqq, hq2, hW, hE, hneg, hadd, hlo, hb, e2, b1, b2, hn, hlt]) (by omega_using [hq, hqq, hq2, hW, hE, hneg, hadd, hlo, hb, e2, b1, b2, hn, hlt])
    have e1 : (S + q + 1) * (q + 1) = (S + q) * q + (S + 2 * q + 1) := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.add_mul]; omega_using []
    have : ((W / 2 : Nat) : Int) = (W : Int) / 2 := by push_cast; rfl
    have ea : addIfNeg E ((R : Int) - ((S + q') * q' : Nat)) = (R : Int) - ((S + (q' - 1)) * (q' - 1) : Nat) := by
      unfold addIfNeg
      simp only [hneg.mpr hlt, ite_true]
      rw [hE (by omega_using [hlt])]
      exact hadd hlt
    rw [← ea]
    refine twos_of_add b1 b2 (by rw [ea]; omega_using [hq, hqq, hq2, hW, hT', hE, h, hneg, hadd, hlo, hb, e2, b1, b2, hn, hlt, hb', e1, this]) (by rw [ea]; omega_using [hq, hqq, hq2, hW, hT', hE, h, hneg, hadd, hlo, hb, e2, b1, b2, hn, hlt, hb', e1, this]) hT hT' hc ?_
    exact h
  · simp only [hlt, ite_false]
    have hnn : ¬ W / 2 ≤ T := fun x => hlt (hn.mp x)
    simp only [hnn, ite_false, Nat.add_zero] at h
    have : c = 0 := by
      rcases (show c = 0 ∨ c = 1 by omega_using [hc]) with e | e
      · exact e
      · exfalso; subst e; have := twos_eq b1 b2; rw [hT] at hnn; omega_using [hq, hqq, hq2, hW, hT, hT', hE, hneg, hadd, hlo, hb, e2, b1, b2, hn, hlt, hnn, hc, h, this]
    subst this
    rw [← hT]; omega_using [h]

/-- The 2-by-1 estimate from the top words is within two above the 3-by-2 one, for
`U < (β + 1) D` and `d ≥ 2^31` (as `WordStepNorm32.qhat3_div`). -/
theorem quot2_bounds {u2 u1 u0 d d1 : Nat} (hu0 : u0 < 2 ^ 32) (hd1 : d1 < 2 ^ 32) (hd : 2 ^ 31 ≤ d) :
    min ((u2 * 2 ^ 64 + u1 * 2 ^ 32 + u0) / (d * 2 ^ 32 + d1)) (2 ^ 32 - 1) ≤ min ((u2 * 2 ^ 32 + u1) / d) (2 ^ 32 - 1) ∧
      min ((u2 * 2 ^ 32 + u1) / d) (2 ^ 32 - 1) ≤
        min ((u2 * 2 ^ 64 + u1 * 2 ^ 32 + u0) / (d * 2 ^ 32 + d1)) (2 ^ 32 - 1) + 2 := by
  have eU : u2 * 2 ^ 64 + u1 * 2 ^ 32 + u0 = (u2 * 2 ^ 32 + u1) * 2 ^ 32 + u0 := by
    rw [Nat.add_mul, Nat.mul_assoc, show (2 : Nat) ^ 32 * 2 ^ 32 = 2 ^ 64 by rw [← Nat.pow_add]]
  rw [eU]
  have h1 := VG.Proof.Bignum.WordStep32.quot_le_div (N := u2 * 2 ^ 32 + u1) (ml := d1) hu0 (by omega_using [hd] : 0 < d)
  refine ⟨Nat.le_min.mpr ⟨Nat.le_trans (Nat.min_le_left _ _) h1, Nat.min_le_right _ _⟩, ?_⟩
  rcases Nat.lt_or_ge (((u2 * 2 ^ 32 + u1) * 2 ^ 32 + u0) / (d * 2 ^ 32 + d1)) (2 ^ 32) with hlt | hge
  · have := VG.Proof.Bignum.WordStep32.div_le_quot (N := u2 * 2 ^ 32 + u1) (yl := u0) hd1 hd hlt
    omega_using [this]
  · omega_using [hge]

/-- `(x >>> 1) ||| ((y &&& 1) ror 1)`: the two words' half. -/
theorem or_half (x y : BitVec 32) :
    (x >>> 1 ||| (y &&& 1).rotateRight 1).toNat = y.toNat % 2 * 2 ^ 31 + x.toNat / 2 := by
  rw [BitVec.toNat_or, VG.Proof.Mont.X86.Dynamic.rotate_lowBit, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, Nat.pow_one]
  have hx : x.toNat / 2 < 2 ^ 31 := by have := x.isLt; omega_using []
  rcases (show y.toNat % 2 = 0 ∨ y.toNat % 2 = 1 by omega_using []) with e | e <;> rw [e]
  · simp
  · rw [Nat.mul_one, VG.Proof.Rsa.X86.WordRt.or_top (by omega_using []), Nat.mod_eq_of_lt hx]; omega_using []

section
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

variable {B : Addr}

/-- Word `i` of the half of the number at `o`: `(w[i + 1] mod 2) 2^31 + ⌊w[i] / 2⌋`. -/
abbrev hw (mem : Mem) (B : Addr) (o i : Nat) : Nat :=
  w32 mem B (o + 4 * (i + 1)) % 2 * 2 ^ 31 + w32 mem B (o + 4 * i) / 2

/-- `halfW p k`: `eax` the word `k` of the half of the number at `p`. -/
theorem halfW_ok {s : State} {is : List Instr} {Q : State → Prop} {bytes : Nat} (ws : Ws s B bytes)
    {p : Reg} {x k : Nat} (hp : PtrAt s B p x) (hx : x + 4 * k + 8 ≤ bytes) (hpc : p ≠ .ecx)
    (kk : ∀ t, Keeps [.eax, .ecx] s t → t.mem = s.mem → (t.gpr .eax).toNat = hw s.mem B x k →
      WP isa (.block is) t Q) :
    WP isa (.block (VG.Impl.Rsa.X86.RecoverDetRt.halfW p k ++ is)) s Q := by
  simp only [VG.Impl.Rsa.X86.RecoverDetRt.halfW, List.cons_append, List.nil_append]
  refine wp_movS (readSrc_ptr ws hp (d := 4 * k + 4) (by omega_using [hx])) fun u₁ U₁ _ => ?_
  refine wp_logicS (.inl rfl) rfl fun u₂ U₂ => wp_ror ⟨by decide, by decide⟩ fun u₃ U₃ => ?_
  have p₃ : PtrAt u₃ B p x := by
    rw [PtrAt, U₃.other _ (Ne.symm hpc.symm), U₂.other _ (Ne.symm hpc.symm), U₁.other _ (Ne.symm hpc.symm)]; exact hp
  have ws₃ : Ws u₃ B bytes := ws.of_wr (by rw [U₃.wr, U₂.wr, U₁.wr])
  refine wp_movS (readSrc_ptr ws₃ p₃ (d := 4 * k) (by omega_using [hx])) fun u₄ U₄ _ => ?_
  refine wp_shr ⟨by decide, by decide⟩ fun u₅ U₅ _ => VG.X86.Wp.wp_or fun u₆ U₆ => ?_
  have m₃ : u₃.mem = s.mem := by rw [U₃.mem, U₂.mem, U₁.mem]
  refine kk u₆ ?_ (by rw [U₆.mem, U₅.mem, U₄.mem, m₃]) ?_
  · exact ((U₁.keeps.mono (by decide)).trans ((U₂.keeps.mono (by decide)).trans (U₃.keeps.mono (by decide)))).trans
      ((U₄.keeps.mono (by decide)).trans ((U₅.keeps.mono (by decide)).trans (U₆.keeps.mono (by decide))))
  · rw [U₆.gpr, U₅.gpr, U₅.other _ (by decide), U₄.gpr, U₄.other _ (by decide), U₃.gpr, U₂.gpr, U₁.gpr, m₃,
      ite_eq_left rfl, or_half]
    simp only [hw, w32, show 4 * (k + 1) = 4 * k + 4 by omega_using []]

end

section
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Proof.Rsa.X86.Keys (Keep arr num S slot)
open VG.Proof.Rsa.X86.KeyRt (RtWs kw)
open VG.Proof.Rsa.X86.WordRt (wq MLen)
open VG.Impl.Rsa.X86.RecoverRt (wid)
open VG.Impl.Rsa.X86.RecoverDetRt (sCt sqZ sqD nl estX)
open VG.Impl.Rsa.X86.WordModRt (oD oV oD1 oU0 oU2 oQ oSteps h0)

variable {B : Addr} {Z len : Nat}

theorem hw_shift (m : Mem) (x e k : Nat) : hw m B (x + 4 * e) k = hw m B x (e + k) := by
  simp only [hw]
  rw [show x + 4 * e + 4 * (k + 1) = x + 4 * (e + k + 1) by omega_using [], show x + 4 * e + 4 * k = x + 4 * (e + k) by omega_using []]

/-- A half word of an array, through header stores. -/
theorem hw_keep {m m' : Mem} {w : Nat} {ds : List Nat} (k : Keep B w [] ds m m')
    (hd : ∀ d ∈ ds, d + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr) {j i : Nat} (hi : 4 * i + 8 ≤ S w)
    (fit : arr w j + S w ≤ 2 ^ 64) : hw m' B (arr w j) i = hw m B (arr w j) i := by
  simp only [hw]
  rw [k.word (j := j) (i := i + 1) (by omega_using [hi]) (by simp) hd fit, k.word (j := j) (i := i) (by omega_using [hi]) (by simp) hd fit]

/-- Three header words changed (from `e`): `Keep` of them. -/
theorem keep_of_three {w : Nat} {js ds : List Nat} {m m' : Mem} {e : Nat} (h : Outside B e 12 m m')
    (h0 : e ∈ ds) (h1 : e + 4 ∈ ds) (h2 : e + 8 ∈ ds) : Keep B w js ds m m' := by
  intro x hx
  have mem : ∀ d ∈ ds, (d, 4) ∈ VG.Proof.Rsa.X86.Keys.ranges w js ds := fun d hd => by
    simp only [VG.Proof.Rsa.X86.Keys.ranges, List.mem_append, List.mem_map]; exact .inr ⟨d, hd, rfl⟩
  have a0 := hx _ (mem _ h0); have a1 := hx _ (mem _ h1); have a2 := hx _ (mem _ h2)
  exact h x (by simp only at a0 a1 a2; omega_using [a0, a1, a2])

theorem oQ_val' : oQ = 76 := rfl

/-- `estX`: `q̂ = min(⌊U / D⌋, β - 1)` at `oQ`, for `U` the top three words of the half of the window
of `sqZ` and `D` the top two of the half of `sqD` (`d` at `oD` and the half of words `W' - 1`,
`W' - 2`), given `quot`'s and `refine3`'s conditions. -/
theorem estX_ok {s : State} (h : RtWs wid s B Z len 22) {a j : Nat} (hm : MLen s B Z nl a)
    (hC : slot s.mem B sCt = j) (hj1 : 1 ≤ j) (hj : j < wq a) (hW : 2 * wq a + 2 ≤ kw len) {d U D : Nat}
    (hD : slot s.mem B oD = d) (hV : slot s.mem B oV = (2 ^ 64 - 1) / d - 2 ^ 32) (hd1 : 2 ^ 31 ≤ d)
    (hU : U = hw s.mem B (arr (kw len) sqZ) (wq a + j - 1) * 2 ^ 64 +
      hw s.mem B (arr (kw len) sqZ) (wq a + j - 2) * 2 ^ 32 + hw s.mem B (arr (kw len) sqZ) (wq a + j - 3))
    (hDd : D = d * 2 ^ 32 + hw s.mem B (arr (kw len) sqD) (wq a - 2))
    (hud : hw s.mem B (arr (kw len) sqZ) (wq a + j - 1) ≤ d) (hUD : U < (2 ^ 32 + 1) * D) :
    WP isa (.block estX) s fun t => RtWs wid t B Z len 22 ∧
      Keep B (kw len) [] [oU0, oD1, oU2, VG.Impl.Bignum.X86.R2Words.oMask h0, oSteps, oQ] s.mem t.mem ∧
      slot t.mem B oQ = min (U / D) (2 ^ 32 - 1) ∧ Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s t := by
  have nw := h.ws.workspace.nowrap
  have hh := h.ws.hdr_le
  have fz := h.ws.arr_fit (j := sqZ) (by decide)
  have fd := h.ws.arr_fit (j := sqD) (by decide)
  have fitz := h.ws.fit64 (j := sqZ) (by decide)
  have fitd := h.ws.fit64 (j := sqD) (by decide)
  simp only [S] at fz fd
  simp only [VG.Impl.Rsa.X86.Keys.hdr] at hh
  have hwa : wq a ≤ 256 := by have := hm.le; simp only [wq]; omega_using [this]
  have hd2 : d < 2 ^ 32 := by rw [← hD]; exact (s.mem.readW _ 32).isLt
  have hdk : ∀ e ∈ [oU0, oD1, oU2, VG.Impl.Bignum.X86.R2Words.oMask h0, oSteps, oQ], e + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr := by
    decide
  have hS : S (kw len) = 4 * (kw len + 2) := rfl
  have e1 : ∀ x, x + 8 * (j - 1) + 4 * (wq a - (j - 1) + 2) - 16 = x + 4 * (wq a + j - 3) := fun x => by omega_using [hj1, hj]
  have e2 : ∀ x, x + 4 * (j - 1) + 4 * (wq a - (j - 1) + 2) - 16 = x + 4 * (wq a - 2) := fun x => by omega_using [hj1, hj]
  have e3 : ∀ x y, 16 ≤ x + y + 4 * (wq a - (j - 1) + 2) := fun x y => by omega_using [hj1, hj]
  -- The half words, read from `s`.
  obtain ⟨u0, hu0⟩ : ∃ u0, hw s.mem B (arr (kw len) sqZ) (wq a + j - 3) = u0 := ⟨_, rfl⟩
  obtain ⟨u1, hu1⟩ : ∃ u1, hw s.mem B (arr (kw len) sqZ) (wq a + j - 2) = u1 := ⟨_, rfl⟩
  obtain ⟨u2, hu2⟩ : ∃ u2, hw s.mem B (arr (kw len) sqZ) (wq a + j - 1) = u2 := ⟨_, rfl⟩
  obtain ⟨d1, hd1'⟩ : ∃ d1, hw s.mem B (arr (kw len) sqD) (wq a - 2) = d1 := ⟨_, rfl⟩
  have hwlt : ∀ (mm : Mem) o i, hw mm B o i < 2 ^ 32 := fun mm o i => by
    have := (mm.readW (off B (o + 4 * i)) 32).isLt
    have := (mm.readW (off B (o + 4 * (i + 1))) 32).isLt
    simp only [hw, w32]; omega_using []
  have lu0 : u0 < 2 ^ 32 := hu0 ▸ hwlt _ _ _
  have lu1 : u1 < 2 ^ 32 := hu1 ▸ hwlt _ _ _
  have ld1 : d1 < 2 ^ 32 := hd1' ▸ hwlt _ _ _
  rw [hu0, hu1, hu2] at hU
  rw [hu2] at hud
  rw [hd1'] at hDd
  unfold estX
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine winPtrs_ok h hm hC hj1 (by omega_using [fz, fd, hW, hj, hj1]) fun u₁ K₁ m₁ ps₁ pb₁ ed₁ _ => ?_
  refine wp_addS rfl fun u₂ U₂ _ => wp_subS rfl fun u₃ U₃ _ => wp_addS rfl fun u₄ U₄ _ =>
    wp_subS rfl fun u₅ U₅ _ => ?_
  have e16 : (16 : BitVec 32).toNat = 16 := rfl
  have ps₂ : PtrAt u₂ B .esi (arr (kw len) sqZ + 8 * (j - 1) + 4 * (wq a - (j - 1) + 2)) := by
    rw [PtrAt, U₂.gpr, ptr_add ps₁, ed₁, Nat.add_assoc]
  have ps₃ : PtrAt u₃ B .esi (arr (kw len) sqZ + 4 * (wq a + j - 3)) := by
    rw [PtrAt, U₃.gpr, ptr_sub ps₂ (16 : BitVec 32) (by rw [e16]; exact e3 _ _), e16,
      e1]
  have pb₃ : PtrAt u₃ B .ebx (arr (kw len) sqD + 4 * (j - 1)) := by
    rw [PtrAt, U₃.other .ebx (by decide), U₂.other .ebx (by decide)]; exact pb₁
  have ed₃ : (u₃.gpr .edx).toNat = 4 * (wq a - (j - 1) + 2) := by
    rw [U₃.other .edx (by decide), U₂.other .edx (by decide)]; exact ed₁
  have pb₄ : PtrAt u₄ B .ebx (arr (kw len) sqD + 4 * (j - 1) + 4 * (wq a - (j - 1) + 2)) := by
    rw [PtrAt, U₄.gpr, ptr_add pb₃, ed₃, Nat.add_assoc]
  have pb₅ : PtrAt u₅ B .ebx (arr (kw len) sqD + 4 * (wq a - 2)) := by
    rw [PtrAt, U₅.gpr, ptr_sub pb₄ (16 : BitVec 32) (by rw [e16]; exact e3 _ _), e16,
      e2]
  have ps₅ : PtrAt u₅ B .esi (arr (kw len) sqZ + 4 * (wq a + j - 3)) := by
    rw [PtrAt, U₅.other _ (by decide), U₄.other _ (by decide)]; exact ps₃
  have K₅ : Keeps [.eax, .ebx, .edx, .esi] s u₅ := K₁.trans ((U₂.keeps.mono (by decide)).trans
    ((U₃.keeps.mono (by decide)).trans ((U₄.keeps.mono (by decide)).trans (U₅.keeps.mono (by decide)))))
  have m₅ : u₅.mem = s.mem := by rw [U₅.mem, U₄.mem, U₃.mem, U₂.mem, m₁]
  -- `u₀`.
  refine halfW_ok (h.rt.of_keeps K₅) ps₅ (k := 0) (by omega_using [fz, fd, hW, hj, hj1]) (by decide) fun u₆ K₆ m₆ e₆ => ?_
  rw [m₅, hw_shift, Nat.add_zero, hu0] at e₆
  have K₆' : Keeps [.eax, .ebx, .ecx, .edx, .esi] s u₆ := (K₅.mono (by decide)).trans (K₆.mono (by decide))
  refine storeHdr (h.ws.rest K₆') (by decide) .eax fun u₇ k₇ s₇ K₇ _ _ => ?_
  rw [e₆] at s₇
  have K₇' : Keeps [.eax, .ebx, .ecx, .edx, .esi] s u₇ := K₆'.trans (K₇.mono (by decide))
  -- `d₁`.
  have pb₇ : PtrAt u₇ B .ebx (arr (kw len) sqD + 4 * (wq a - 2)) := by
    rw [PtrAt, K₇.1 _ (by decide), K₆.1 _ (by decide)]; exact pb₅
  refine halfW_ok (h.rt.of_keeps K₇') pb₇ (k := 0) (by omega_using [fz, fd, hW, hj, hj1]) (by decide) fun u₈ K₈ m₈ e₈ => ?_
  have k₇' : Keep B (kw len) [] [oU0] s.mem u₇.mem := by rw [← m₅, ← m₆]; exact k₇
  rw [hw_shift, Nat.add_zero, hw_keep k₇' (by decide) (by rw [hS]; omega_using [hW, hj, hj1]) fitd, hd1'] at e₈
  have K₈' : Keeps [.eax, .ebx, .ecx, .edx, .esi] s u₈ := K₇'.trans (K₈.mono (by decide))
  refine storeHdr (h.ws.rest K₈') (by decide) .eax fun u₉ k₉ s₉ K₉ _ _ => ?_
  rw [e₈] at s₉
  have K₉' : Keeps [.eax, .ebx, .ecx, .edx, .esi] s u₉ := K₈'.trans (K₉.mono (by decide))
  have k₉' : Keep B (kw len) [] [oU0, oD1] s.mem u₉.mem :=
    (k₇'.mono (by simp) (by simp)).trans (by rw [← m₈]; exact k₉.mono (by simp) (by simp))
  -- `u₂`.
  have ps₉ : PtrAt u₉ B .esi (arr (kw len) sqZ + 4 * (wq a + j - 3)) := by
    rw [PtrAt, K₉.1 _ (by decide), K₈.1 _ (by decide), K₇.1 _ (by decide), K₆.1 _ (by decide)]; exact ps₅
  refine halfW_ok (h.rt.of_keeps K₉') ps₉ (k := 2) (by omega_using [fz, fd, hW, hj, hj1]) (by decide) fun u₁₀ K₁₀ m₁₀ e₁₀ => ?_
  rw [hw_shift, hw_keep k₉' (by decide) (by rw [hS]; omega_using [hW, hj, hj1]) fitz, show wq a + j - 3 + 2 = wq a + j - 1 by omega_using [hj, hj1],
    hu2] at e₁₀
  have K₁₀' : Keeps [.eax, .ebx, .ecx, .edx, .esi] s u₁₀ := K₉'.trans (K₁₀.mono (by decide))
  refine storeHdr (h.ws.rest K₁₀') (by decide) .eax fun u₁₁ k₁₁ s₁₁ K₁₁ _ _ => ?_
  rw [e₁₀] at s₁₁
  refine wp_movS rfl fun u₁₂ U₁₂ _ => ?_
  have K₁₂' : Keeps [.eax, .ebx, .ecx, .edx, .esi] s u₁₂ := K₁₀'.trans ((K₁₁.mono (by decide)).trans
    (U₁₂.keeps.mono (by decide)))
  have m₁₂ : u₁₂.mem = u₁₁.mem := U₁₂.mem
  have k₁₂ : Keep B (kw len) [] [oU0, oD1, oU2] s.mem u₁₂.mem :=
    (k₉'.mono (by simp) (by simp)).trans (by rw [m₁₂, ← m₁₀]; exact k₁₁.mono (by simp) (by simp))
  have dx₁₂ : (u₁₂.gpr .edx).toNat = u2 := by rw [U₁₂.gpr, K₁₁.1 _ (by decide)]; exact e₁₀
  -- `u₁`.
  have ps₁₂ : PtrAt u₁₂ B .esi (arr (kw len) sqZ + 4 * (wq a + j - 3)) := by
    rw [PtrAt, U₁₂.other _ (by decide), K₁₁.1 _ (by decide), K₁₀.1 _ (by decide)]; exact ps₉
  refine halfW_ok (h.rt.of_keeps K₁₂') ps₁₂ (k := 1) (by omega_using [fz, fd, hW, hj, hj1]) (by decide) fun u₁₃ K₁₃ m₁₃ e₁₃ => ?_
  rw [hw_shift, hw_keep k₁₂ (by decide) (by rw [hS]; omega_using [hW, hj, hj1]) fitz, show wq a + j - 3 + 1 = wq a + j - 2 by omega_using [hj, hj1],
    hu1] at e₁₃
  refine wp_movS rfl fun u₁₄ U₁₄ _ => wp_movS rfl fun u₁₅ U₁₅ _ => ?_
  have K₁₅ : Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s u₁₅ := (K₁₂'.mono (by decide)).trans
    ((K₁₃.mono (by decide)).trans ((U₁₄.keeps.mono (by decide)).trans (U₁₅.keeps.mono (by decide))))
  have m₁₅ : u₁₅.mem = u₁₂.mem := by rw [U₁₅.mem, U₁₄.mem, m₁₃]
  have k₁₅ : Keep B (kw len) [] [oU0, oD1, oU2] s.mem u₁₅.mem := by rw [m₁₅]; exact k₁₂
  have ax₁₅ : u₁₅.gpr .eax = BitVec.ofNat 32 u2 := by
    rw [U₁₅.gpr, U₁₄.other _ (by decide), K₁₃.1 _ (by decide), ← dx₁₂, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have bp₁₅ : u₁₅.gpr .ebp = BitVec.ofNat 32 u1 := by
    rw [U₁₅.other _ (by decide), U₁₄.gpr, ← e₁₃, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have di₁₅ : PtrAt u₁₅ B .edi 0 := by
    rw [PtrAt, K₁₅.1 _ (by decide), h.edi, Nat.add_zero, Nat.mod_eq_of_lt (by omega_using [nw, hh])]
  -- The header words `quot` and `refine3` read.
  have sl : ∀ e, e + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr → (∀ f ∈ [oU0, oD1, oU2], e + 4 ≤ f ∨ f + 4 ≤ e) →
      w32 u₁₅.mem B e = slot s.mem B e := fun e he hf => k₁₅.slot he hf
  have wD : w32 u₁₅.mem B (VG.Impl.Bignum.X86.R2Words.oD h0) = d := (sl oD (by decide) (by decide)).trans hD
  have wV : w32 u₁₅.mem B (VG.Impl.Bignum.X86.R2Words.oV h0) = (2 ^ 64 - 1) / d - 2 ^ 32 :=
    (sl oV (by decide) (by decide)).trans hV
  have hu2d : u2 ≤ d := hud
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Bignum.X86.R2Words.WP.keeps [.eax, .ebx, .ecx, .edx, .esi]
    (VG.Proof.Bignum.X86.R2Words.quot_ok (h := h0) (h.rt.of_keeps K₁₅) di₁₅ (by simp only [h0]; omega_using [hh])
      ax₁₅ bp₁₅ wD wV hd1 hd2 hu2d lu1) rfl) fun t₁ ⟨⟨q₁, O₁, _, K₁'⟩, KK⟩ => ?_
  rw [VG.Proof.Bignum.WordTop32.qhat_min hu2d lu1 (by omega_using [hd1])] at q₁
  have K₁₆ : Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s t₁ := K₁₅.trans K₁'
  have di₁₆ : PtrAt t₁ B .edi 0 := by rw [PtrAt, K₁'.1 _ (by decide)]; exact di₁₅
  have bp₁₆ : t₁.gpr .ebp = BitVec.ofNat 32 u1 := (KK.1 _ (by decide)).trans bp₁₅
  have w₁ : ∀ e, e + 4 ≤ 68 → w32 t₁.mem B e = w32 u₁₅.mem B e := fun e he =>
    O₁.w32 (.inl (by simp only [VG.Impl.Bignum.X86.R2Words.oMask, h0]; omega_using [he])) (by omega_using [he])
  have w₁' : ∀ e, 80 ≤ e → e + 4 ≤ 160 → w32 t₁.mem B e = w32 u₁₅.mem B e := fun e he he' =>
    O₁.w32 (.inr (by simp only [VG.Impl.Bignum.X86.R2Words.oMask, h0]; omega_using [he])) (by omega_using [he'])
  have sU0 : w32 u₁₅.mem B oU0 = u0 := by
    rw [m₁₅, m₁₂]
    refine (k₁₁.slot (e := oU0) (by decide) (by decide)).trans ?_
    rw [m₁₀]
    refine (k₉.slot (e := oU0) (by decide) (by decide)).trans ?_
    rw [m₈]; exact s₇
  have sD1 : w32 u₁₅.mem B oD1 = d1 := by
    rw [m₁₅, m₁₂]
    refine (k₁₁.slot (e := oD1) (by decide) (by decide)).trans ?_
    rw [m₁₀]; exact s₉
  have sU2 : w32 u₁₅.mem B oU2 = u2 := by rw [m₁₅, m₁₂]; exact s₁₁
  have eU0 : w32 t₁.mem B (VG.Impl.Bignum.X86.R2Words.oU0 h0) = u0 := (w₁' _ (by decide) (by decide)).trans sU0
  have eU2 : w32 t₁.mem B (VG.Impl.Bignum.X86.R2Words.oU2 h0) = u2 := (w₁' _ (by decide) (by decide)).trans sU2
  have eD1 : w32 t₁.mem B (VG.Impl.Bignum.X86.R2Words.oD1 h0) = d1 := (w₁' _ (by decide) (by decide)).trans sD1
  have eD : w32 t₁.mem B (VG.Impl.Bignum.X86.R2Words.oD h0) = d := (w₁ _ (by decide)).trans wD
  have qb := quot2_bounds (u2 := u2) (u1 := u1) lu0 ld1 hd1
  refine WP.mono (VG.Proof.Bignum.X86.R2Words.refine3_ok (h := h0) (h.rt.of_keeps K₁₆) di₁₆
    (by simp only [h0]; omega_using [hh]) (U := U) (D := D)
    (by rw [eU2, bp₁₆, eU0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt lu1, hU])
    (by rw [eD, eD1, hDd]) (by rw [hDd]; omega_using [hd1]) hUD
    (by rw [q₁, hU, hDd]; exact qb.1) (by rw [q₁, hU, hDd]; exact qb.2)) fun t₂ ⟨m₂, K₂⟩ => ?_
  have hQ : min (U / D) (2 ^ 32 - 1) < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by decide)
  have Kall : Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s t₂ := K₁₆.trans K₂
  have k3 : Keep B (kw len) [] [oU0, oD1, oU2, VG.Impl.Bignum.X86.R2Words.oMask h0, oSteps, oQ] u₁₅.mem t₁.mem :=
    keep_of_three O₁ (by simp) (by decide) (by decide)
  have kQ : Keep B (kw len) [] [oU0, oD1, oU2, VG.Impl.Bignum.X86.R2Words.oMask h0, oSteps, oQ] t₁.mem t₂.mem :=
    Keep.of_slot (by rw [m₂]; exact writeW32_outside _ B _ (by decide)) (by simp)
  have kO : Keep B (kw len) [] [oU0, oD1, oU2, VG.Impl.Bignum.X86.R2Words.oMask h0, oSteps, oQ] s.mem t₂.mem :=
    ((k₁₅.mono (by simp) (by simp)).trans k3).trans kQ
  refine ⟨h.keep Kall (by decide) (by decide) (VG.Proof.Rsa.X86.KeyRt.keep_outside h.ws kO (by simp) hdk), kO, ?_, Kall⟩
  show w32 t₂.mem B oQ = _
  rw [m₂, w32_write_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hQ]

end

/-! ## Windows of numbers -/

section
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

variable {B : Addr}

/-- `K` words of a number from word `i`. -/
theorem val32_win (m : Mem) (d i K n : Nat) (h : i + K ≤ n) :
    val32 m B (d + 4 * i) K = val32 m B d n / 2 ^ (32 * i) % 2 ^ (32 * K) := by
  obtain ⟨r, rfl⟩ : ∃ r, n = i + (K + r) := ⟨n - i - K, by omega_using [h]⟩
  rw [VG.Proof.Rsa.X86.WordRt.val32_high, VG.Proof.Rsa.X86.Recover.val32_mod]

/-- A number whose words from `i` to `i + K` changed. -/
theorem val32_splice {m m' : Mem} {d i K n : Nat} (hn : i + K ≤ n)
    (h : ∀ k, k < n → (k < i ∨ i + K ≤ k) → w32 m' B (d + 4 * k) = w32 m B (d + 4 * k)) :
    val32 m' B d n + val32 m B (d + 4 * i) K * 2 ^ (32 * i) =
      val32 m B d n + val32 m' B (d + 4 * i) K * 2 ^ (32 * i) := by
  obtain ⟨r, rfl⟩ : ∃ r, n = i + (K + r) := ⟨n - i - K, by omega_using [hn]⟩
  rw [val32_append, val32_append m, val32_append m' B (d + 4 * i), val32_append m B (d + 4 * i)]
  have lo : val32 m' B d i = val32 m B d i := val32_congr fun k hk => h k (by omega_using [hk]) (.inl hk)
  have hi : val32 m' B (d + 4 * i + 4 * K) r = val32 m B (d + 4 * i + 4 * K) r := val32_congr fun k hk => by
    rw [show d + 4 * i + 4 * K + 4 * k = d + 4 * (i + K + k) by omega_using []]
    exact h _ (by omega_using [hk]) (.inr (by omega_using []))
  rw [lo, hi]
  generalize val32 m B d i = A; generalize val32 m B (d + 4 * i + 4 * K) r = H
  generalize val32 m' B (d + 4 * i) K = x'; generalize val32 m B (d + 4 * i) K = x
  generalize 2 ^ (32 * i) = G; generalize 2 ^ (32 * K) = G2
  grind

theorem wd_shift (x c i : Nat) : wd x (c + i) = wd (x / 2 ^ (32 * c)) i := by
  simp only [wd]; rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.mul_add]

/-- A half word of a number of `n` words. -/
theorem hw_val (m : Mem) (o i n : Nat) (h : i + 1 < n) : hw m B o i = wd (val32 m B o n / 2) i := by
  rw [half_wd]
  simp only [hw, wd]
  rw [VG.Proof.Rsa.X86.WordRt.w32_of_val32 m B (n := n) (by omega_using [h]),
    VG.Proof.Rsa.X86.WordRt.w32_of_val32 m B (n := n) (by omega_using [h])]

/-- Three words from word `k`. -/
theorem words3 (x k : Nat) (h : x / 2 ^ (32 * k) < 2 ^ 96) :
    wd x (k + 2) * 2 ^ 64 + wd x (k + 1) * 2 ^ 32 + wd x k = x / 2 ^ (32 * k) := by
  rw [wd_shift x k 2, wd_shift x k 1, show wd x k = wd x (k + 0) from rfl, wd_shift x k 0]
  obtain ⟨y, ey⟩ : ∃ y, x / 2 ^ (32 * k) = y := ⟨_, rfl⟩
  rw [ey] at h ⊢
  simp only [wd, Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.reducePow, Nat.reduceMul] at h ⊢
  omega_using [h]

/-- The top two words of `s β` from word `k`: `s`'s word `k` and the word below it. -/
theorem top2_words (s k : Nat) :
    s * 2 ^ 32 / 2 ^ (32 * k) = s / 2 ^ (32 * k) * 2 ^ 32 + wd (s * 2 ^ 32) k := by
  have e : s * 2 ^ 32 / 2 ^ (32 * k) / 2 ^ 32 = s / 2 ^ (32 * k) := by
    rw [Nat.div_div_eq_div_mul, Nat.mul_div_mul_right _ _ (show 0 < 2 ^ 32 by decide)]
  simp only [wd]
  rw [← e]; exact (Nat.div_add_mod' _ _).symm

end

/-- `R - (S + q') q'` is within `[-W / 2, W / 2)` for `q ≤ q' ≤ q + 2`. -/
theorem twos_bounds {W S R q q' : Nat} (hq : (S + q) * q ≤ R ∧ R < (S + (q + 1)) * (q + 1))
    (hqq : q ≤ q') (hq2 : q' ≤ q + 2) (hW : R + 2 * S + 4 * q + 4 < W / 2) :
    -((W : Int) / 2) ≤ (R : Int) - ((S + q') * q' : Nat) ∧ (R : Int) - ((S + q') * q' : Nat) < (W : Int) / 2 := by
  have hlo : (S + q) * q ≤ R := hq.1
  have hb : (S + q') * q' ≤ (S + q + 2) * (q + 2) := Nat.mul_le_mul (by omega) hq2
  have e2 : (S + q + 2) * (q + 2) = (S + q) * q + (2 * S + 4 * q + 4) := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.add_mul]; omega_using []
  have : ((W / 2 : Nat) : Int) = (W : Int) / 2 := by push_cast; rfl
  constructor <;> omega_arith

section
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Proof.Rsa.X86.Keys (Keep arr num S slot)
open VG.Proof.Rsa.X86.KeyRt (RtWs kw)
open VG.Proof.Rsa.X86.WordRt (wq MLen)
open VG.Impl.Rsa.X86.RecoverRt (wid)
open VG.Impl.Rsa.X86.RecoverDetRt (sCt sqZ sqD sqT nl hCnt fixX)
open VG.Impl.Rsa.X86.WordModRt (oD oV oD1 oU0 oU2 oQ oSteps h0)
open VG.Proof.Bignum.WordStep32 (twos)

variable {B : Addr} {Z len : Nat}

/-- The pair of `sqD`'s words `m`, `m + 1` (`m = j - 1`). -/
abbrev pr (mem : Mem) (B : Addr) (len j : Nat) : Nat :=
  w32 mem B (arr (kw len) sqD + 4 * (j - 1)) + 2 ^ 32 * w32 mem B (arr (kw len) sqD + 4 * (j - 1) + 4)

/-- The header words a digit step writes, but `sCt`. -/
abbrev stepDs : List Nat := [oU0, oD1, oU2, VG.Impl.Bignum.X86.R2Words.oMask h0, oSteps, oQ, hCnt]

/-- Between the corrections of a digit step from `x`: the remainder `T` for the estimate `q'`
(`q ≤ q' ≤ q + 2`, `q` the digit) in two's complement, and `sqD`'s pair `y β + 2 q' - 1`. -/
structure FixI (B : Addr) (Z len : Nat) (x : State) (a j S R y q q' : Nat) (v : State) : Prop where
  rt : RtWs wid v B Z len 22
  hm : MLen v B Z nl a
  keep : Keep B (kw len) [sqT, sqD] stepDs x.mem v.mem
  dw : ∀ i, i < kw len + 2 → i ≠ j - 1 → i ≠ j →
    w32 v.mem B (arr (kw len) sqD + 4 * i) = w32 x.mem B (arr (kw len) sqD + 4 * i)
  pair : (pr v.mem B len j + 1) % 2 ^ 64 = y * 2 ^ 32 + 2 * q'
  T : val32 v.mem B (arr (kw len) sqT) (wq a - (j - 1) + 3) =
    twos (2 ^ (32 * (wq a - (j - 1) + 3))) ((R : Int) - ((S + q') * q' : Nat))
  q1 : q ≤ q'
  q2 : q' ≤ q + 2
  q3 : q' < 2 ^ 32
  keeps : Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] x v

theorem pr_lt (mem : Mem) (len j : Nat) : pr mem B len j < 2 ^ 64 := by
  have := (mem.readW (off B (arr (kw len) sqD + 4 * (j - 1))) 32).isLt
  have := (mem.readW (off B (arr (kw len) sqD + 4 * (j - 1) + 4)) 32).isLt
  simp only [pr, w32]; omega_using []

/-- A correction. -/
theorem fix_ok {x v : State} {a j S R y Dh q q' : Nat} (I : FixI B Z len x a j S R y q q' v)
    (hC : slot x.mem B sCt = j) (hj1 : 1 ≤ j) (hj : j < wq a) (hW : wq a + 3 ≤ kw len)
    (hq : (S + q) * q ≤ R ∧ R < (S + (q + 1)) * (q + 1))
    (hWb : R + 2 * S + 4 * q + 4 < 2 ^ (32 * (wq a - (j - 1) + 3)) / 2)
    (hDh : val32 x.mem B (arr (kw len) sqD + 4 * (j - 1) + 8) (wq a - (j - 1) + 1) = Dh)
    (hS : S = Dh * 2 ^ 64 + y * 2 ^ 32) :
    WP isa fixX v (FixI B Z len x a j S R y q (if q < q' then q' - 1 else q')) := by
  have hCv : slot v.mem B sCt = j := (I.keep.slot (e := sCt) (by decide) (by decide)).trans hC
  refine WP.mono (fixX_ok I.rt I.hm hCv hj1 hj hW) fun t ⟨rt, k, dw, ⟨c, hc, hT⟩, hp, K⟩ => ?_
  obtain ⟨L, eL⟩ : ∃ L, wq a - (j - 1) + 2 = L := ⟨_, rfl⟩
  have IT := I.T
  have e3 : wq a - (j - 1) + 3 = L + 1 := by omega_using [eL]
  rw [e3] at hT IT hWb
  rw [show wq a - (j - 1) + 1 = L - 1 by omega_using [eL]] at hDh
  rw [eL] at hT hp
  have hL : 2 ≤ L := by omega_using [eL]
  -- The top bit of `T`.
  have topIff : 2 ^ (32 * (L + 1)) / 2 ≤ val32 v.mem B (arr (kw len) sqT) (L + 1) ↔
      2 ^ 31 ≤ w32 v.mem B (arr (kw len) sqT + 4 * L) := by
    rw [val32_succ]; exact VG.Proof.Bignum.WordTop32.topBit_iff (val32_lt _ _ _ _) (v.mem.readW _ 32).isLt
  -- The window of `sqD`.
  have win : 1 ≤ q' → val32 v.mem B (arr (kw len) sqD + 4 * (j - 1)) (L + 1) = S + 2 * q' - 1 := by
    intro h1
    rw [show L + 1 = 2 + (L - 1) by omega_using [eL], val32_append]
    have e2 : val32 v.mem B (arr (kw len) sqD + 4 * (j - 1)) 2 = pr v.mem B len j := by
      simp only [val32, pr]; omega_using []
    have et : val32 v.mem B (arr (kw len) sqD + 4 * (j - 1) + 4 * 2) (L - 1) = Dh := by
      rw [← hDh]
      refine val32_congr fun i hi => ?_
      rw [show arr (kw len) sqD + 4 * (j - 1) + 4 * 2 + 4 * i = arr (kw len) sqD + 4 * (j - 1 + 2 + i) by omega_using []]
      exact I.dw _ (by omega_using [hj, hW, eL, hi]) (by omega_using []) (by omega_using [])
    rw [e2, et]
    have hp1 := I.pair
    have hpl := pr_lt (B := B) v.mem len j
    have hq3 := I.q3
    rw [hS]
    simp only [Nat.reducePow, Nat.reduceMul] at hp1 hpl hq3 ⊢
    omega_using [h1, hp1, hpl]
  have hrel : val32 t.mem B (arr (kw len) sqT) (L + 1) + 2 ^ (32 * (L + 1)) * c =
      val32 v.mem B (arr (kw len) sqT) (L + 1) +
        if 2 ^ (32 * (L + 1)) / 2 ≤ val32 v.mem B (arr (kw len) sqT) (L + 1)
        then val32 v.mem B (arr (kw len) sqD + 4 * (j - 1)) (L + 1) else 0 := by
    rw [hT]
    by_cases hn : 2 ^ 31 ≤ w32 v.mem B (arr (kw len) sqT + 4 * L)
    · simp only [hn, topIff.mpr hn, ite_true]
    · simp only [hn, mt topIff.mp hn, ite_false]
  obtain ⟨hneg, hT'⟩ := fix_step hq I.q1 I.q2 hWb IT (val32_lt _ _ _ _) hc win hrel
  have hcond : (2 ^ 31 ≤ w32 v.mem B (arr (kw len) sqT + 4 * L)) ↔ q < q' := topIff.symm.trans hneg
  have hrt := rt
  refine ⟨rt, I.hm.keep K (by decide) (VG.Proof.Rsa.X86.KeyRt.keep_outside I.rt.ws k (by decide) (by decide)),
    I.keep.trans (k.mono (by simp) (by simp)), fun i hi h1 h2 => (dw i hi h1 h2).trans (I.dw i hi h1 h2),
    ?_, by rw [e3]; exact hT', ?_, ?_, ?_, I.keeps.trans K⟩
  · have hp1 := I.pair
    have hpl := pr_lt (B := B) v.mem len j
    have hq3 := I.q3
    have hc' : (2 ^ 31 ≤ w32 v.mem B (arr (kw len) sqT + 4 * (wq a - (j - 1) + 2))) ↔ q < q' := by
      rw [eL]; exact hcond
    have hp' : pr t.mem B len j = (pr v.mem B len j + 2 ^ 64 -
        if 2 ^ 31 ≤ w32 v.mem B (arr (kw len) sqT + 4 * (wq a - (j - 1) + 2)) then 2 else 0) % 2 ^ 64 := by
      rw [eL]; exact hp
    rw [hp']
    obtain ⟨P, eP⟩ : ∃ P, pr v.mem B len j = P := ⟨_, rfl⟩
    rw [eP] at hp1 hpl ⊢
    by_cases hlt : q < q'
    · simp only [hc'.mpr hlt, hlt, ite_true]
      have h1 : 1 ≤ q' := by omega_using [hlt]
      simp only [Nat.reducePow] at hp1 hpl hq3 ⊢
      omega_using [hp1, hpl, hq3, h1]
    · simp only [mt hc'.mp hlt, hlt, ite_false]
      simp only [Nat.reducePow] at hp1 hpl hq3 ⊢
      omega_using [hp1, hpl, hq3]
  · have := I.q1; split <;> omega_arith
  · have := I.q2; split <;> omega_using [this]
  · have := I.q3; split <;> omega_using [this]

/-- Words of an array through a `Keep` that leaves it. -/
theorem keep_val32 {m m' : Mem} {w : Nat} {js ds : List Nat} (k : Keep B w js ds m m') {jj i K : Nat}
    (hj : ∀ k ∈ js, k ≠ jj) (hd : ∀ d ∈ ds, d + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr) (fit : arr w jj + S w ≤ 2 ^ 64)
    (hK : 4 * (i + K) ≤ S w) : val32 m' B (arr w jj + 4 * i) K = val32 m B (arr w jj + 4 * i) K :=
  val32_congr fun t ht => by
    rw [show arr w jj + 4 * i + 4 * t = arr w jj + 4 * (i + t) by omega_using []]
    exact k.word (by omega_using [hK, ht]) hj hd fit

/-- From after `estX`: `mulSubX` and `toE` give the corrections' invariant for `q̂ = Q`. -/
theorem pre_ok {x v₁ : State} {a j S R y q Q Dh : Nat} {rest : Prog isa} {Qp : State → Prop}
    (h₁ : RtWs wid v₁ B Z len 22) (hm₁ : MLen v₁ B Z nl a)
    (k₁ : Keep B (kw len) [] stepDs x.mem v₁.mem) (K₁ : Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] x v₁)
    (hC : slot x.mem B sCt = j) (hQ : slot v₁.mem B oQ = Q) (hj1 : 1 ≤ j) (hj : j < wq a) (hW : wq a + 3 ≤ kw len) (hW2 : 2 * wq a + 2 ≤ kw len)
    (hZw : val32 x.mem B (arr (kw len) sqZ + 8 * (j - 1)) (wq a - (j - 1) + 3) = R)
    (hD1 : w32 x.mem B (arr (kw len) sqD + 4 * (j - 1) + 4) = y)
    (hDw : val32 x.mem B (arr (kw len) sqD + 4 * (j - 1) + 4) (wq a - (j - 1) + 1) = Dh * 2 ^ 32 + y)
    (hS : S = Dh * 2 ^ 64 + y * 2 ^ 32) (hy : y % 2 = 0)
    (hq : (S + q) * q ≤ R ∧ R < (S + (q + 1)) * (q + 1)) (hQ1 : q ≤ Q) (hQ2 : Q ≤ q + 2) (hQ3 : Q < 2 ^ 32)
    (hWb : R + 2 * S + 4 * q + 4 < 2 ^ (32 * (wq a - (j - 1) + 3)) / 2)
    (k : ∀ v, FixI B Z len x a j S R y q Q v → WP isa rest v Qp) :
    WP isa (.seq VG.Impl.Rsa.X86.RecoverDetRt.mulSubX (.seq (.block VG.Impl.Rsa.X86.RecoverDetRt.toE) rest)) v₁ Qp := by
  have fitD := h₁.ws.fit64 (j := sqD) (by decide)
  have fitT := h₁.ws.fit64 (j := sqT) (by decide)
  obtain ⟨-, eD, eT⟩ := sq_arrs (kw len)
  have hdk : ∀ e ∈ stepDs, e + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr := by decide
  have hC₁ : slot v₁.mem B sCt = j := (k₁.slot (e := sCt) (by decide) (by decide)).trans hC
  have hy2 : y < 2 ^ 32 := hD1 ▸ (x.mem.readW _ 32).isLt
  refine WP.seq (WP.mono (mulSubX_ok h₁ hm₁ hC₁ hj1 hj hW hQ) fun v₂ ⟨h₂, k₂, dw₂, d₂, ⟨b, hb, hT₂⟩, K₂⟩ => ?_)
  have hm₂ : MLen v₂ B Z nl a :=
    hm₁.keep K₂ (by decide) (VG.Proof.Rsa.X86.KeyRt.keep_outside h₁.ws k₂ (by decide) (by decide))
  have hC₂ : slot v₂.mem B sCt = j := (k₂.slot (e := sCt) (by decide) (by decide)).trans hC₁
  refine WP.seq (WP.mono (toE_ok h₂ hm₂ hC₂ hj1 hj hW) fun v₃ ⟨h₃, O₃, p₃, K₃⟩ => k v₃ ?_)
  -- `sqD`'s words through `estX` and `mulSubX`.
  have dw₁₂ : ∀ i, i < kw len + 2 → i ≠ j - 1 →
      w32 v₂.mem B (arr (kw len) sqD + 4 * i) = w32 x.mem B (arr (kw len) sqD + 4 * i) := fun i hi h1 =>
    (dw₂ i hi h1).trans (k₁.word (by simp only [VG.Proof.Rsa.X86.Keys.S]; omega_using [hi]) (by simp) hdk fitD)
  have tail : val32 v₂.mem B (arr (kw len) sqD + 4 * (j - 1) + 4) (wq a - (j - 1) + 1) = Dh * 2 ^ 32 + y :=
    (val32_congr fun i hi => by
      rw [show arr (kw len) sqD + 4 * (j - 1) + 4 + 4 * i = arr (kw len) sqD + 4 * (j - 1 + 1 + i) by omega_using []]
      exact dw₁₂ _ (by omega_using [hj, hW, hi]) (by omega_using [])).trans hDw
  have hwin : val32 v₂.mem B (arr (kw len) sqD + 4 * (j - 1)) (wq a - (j - 1) + 2) = S + Q := by
    rw [show wq a - (j - 1) + 2 = (wq a - (j - 1) + 1) + 1 by omega_using [], val32, d₂, tail, hS]
    omega_using []
  have hZ₁ : val32 v₁.mem B (arr (kw len) sqZ + 8 * (j - 1)) (wq a - (j - 1) + 3) = R := by
    rw [show arr (kw len) sqZ + 8 * (j - 1) = arr (kw len) sqZ + 4 * (2 * (j - 1)) by omega_using [],
      keep_val32 k₁ (by simp) hdk (h₁.ws.fit64 (j := sqZ) (by decide))
        (by simp only [VG.Proof.Rsa.X86.Keys.S]; omega_using [hj, hW2]),
      show arr (kw len) sqZ + 4 * (2 * (j - 1)) = arr (kw len) sqZ + 8 * (j - 1) by omega_using []]
    exact hZw
  rw [hwin] at hT₂
  obtain ⟨bl1, bl2⟩ := twos_bounds (W := 2 ^ (32 * (wq a - (j - 1) + 3))) hq hQ1 hQ2 hWb
  have hT₂' : val32 v₂.mem B (arr (kw len) sqT) (wq a - (j - 1) + 3) =
      twos (2 ^ (32 * (wq a - (j - 1) + 3))) ((R : Int) - ((S + Q) * Q : Nat)) :=
    VG.Proof.Bignum.WordStep32.twos_of_sub (val32_lt _ _ _ _) hb
      (by rw [Nat.mul_comm (S + Q) Q, ← hZ₁]; exact hT₂) bl1 bl2
  have k₃ : Keep B (kw len) [sqT, sqD] stepDs v₂.mem v₃.mem :=
    Keep.of_arr (d := 4 * (j - 1)) (n := 8) O₃ (by simp only [VG.Proof.Rsa.X86.Keys.S]; omega_using [hj, hW]) (by simp)
  refine ⟨h₃, hm₂.keep K₃ (by decide) (VG.Proof.Rsa.X86.KeyRt.keep_outside h₂.ws k₃ (by decide) hdk),
    (k₁.mono (by simp) (by simp)).trans ((k₂.mono (by simp) (by simp)).trans k₃), fun i hi h1 h2 => ?_, ?_, ?_,
    hQ1, hQ2, hQ3, K₁.trans ((K₂.trans (K₃.mono (by decide))))⟩
  · rw [O₃.w32 (by omega_using [hj1, h1, h2]) (by omega_using [fitT, eD, eT, hi])]; exact dw₁₂ i hi h1
  · have hp : pr v₃.mem B len j = _ := p₃
    have hy₂ : w32 v₂.mem B (arr (kw len) sqD + 4 * (j - 1) + 4) = y := by
      rw [show arr (kw len) sqD + 4 * (j - 1) + 4 = arr (kw len) sqD + 4 * (j - 1 + 1) by omega_using [],
        dw₁₂ _ (by omega_using [hj, hW]) (by omega_using []), show arr (kw len) sqD + 4 * (j - 1 + 1) = arr (kw len) sqD + 4 * (j - 1) + 4 by omega_using []]
      exact hD1
    rw [hp, d₂, hy₂]
    simp only [Nat.reducePow] at hQ3 hy2 ⊢
    omega_using [hQ3, hy2, hy]
  · have ft := fitT
    simp only [VG.Proof.Rsa.X86.Keys.S] at ft
    rw [O₃.val32 (.inr (by rw [eD, eT]; omega_using [hj, hW])) (by omega_using [ft, hW])]; exact hT₂'

/-- The count block: `sCt := j - 1`, ZF where it is zero. -/
theorem count_ok {v : State} {Qp : State → Prop} (h : RtWs wid v B Z len 22) {j : Nat}
    (hC : slot v.mem B sCt = j) (hj1 : 1 ≤ j) (hj32 : j < 2 ^ 32)
    (k : ∀ t, Keep B (kw len) [] [sCt] v.mem t.mem → slot t.mem B sCt = j - 1 → Keeps [.eax] v t →
      t.zf = some (decide (j - 1 = 0)) → Qp t) :
    WP isa (.block [.mov .eax (.mem (sc sCt)), .alu .sub .eax (.imm 1), .store (sc sCt) .eax]) v Qp := by
  refine wp_movS (readHdr h.ws (by decide)) fun u₁ U₁ _ => VG.Proof.Mont.X86.Rt.wp_subZ rfl fun u₂ U₂ z₂ => ?_
  have e : u₂.gpr .eax = BitVec.ofNat 32 (j - 1) := by
    rw [U₂.gpr, U₁.gpr, hC]; exact VG.X86.Wp.ofNat_pred hj1
  refine storeHdr (h.ws.rest (U₁.keeps.trans U₂.keeps)) (by decide) .eax fun t kt st Kt zt _ => WP.block_nil ?_
  refine k t (by rw [U₂.mem, U₁.mem] at kt; exact kt) ?_ ((U₁.keeps.trans U₂.keeps).trans (Kt.mono (by simp))) ?_
  · rw [st, e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hj32])]
  · rw [zt, z₂, ← U₂.gpr, e, VG.X86.Wp.ofNat_beq_zero (by omega_using [hj32])]

/-- After the corrections (`q' = q`): `updX`, `copyBackX` and the count. -/
theorem post_ok {x v : State} {a j S R y q : Nat} {Qp : State → Prop} (I : FixI B Z len x a j S R y q q v)
    (hC : slot x.mem B sCt = j) (hj1 : 1 ≤ j) (hj : j < wq a) (hW : wq a + 3 ≤ kw len)
    (hW2 : 2 * wq a + 2 ≤ kw len) (hq : (S + q) * q ≤ R)
    (hWb : R < 2 ^ (32 * (wq a - (j - 1) + 3)) / 2)
    (k : ∀ t, RtWs wid t B Z len 22 → Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] x t →
      Keep B (kw len) [sqZ, sqD, sqT] (sCt :: stepDs) x.mem t.mem →
      slot t.mem B sCt = j - 1 → t.zf = some (decide (j - 1 = 0)) →
      (∀ i, i < kw len + 2 → i ≠ j - 1 → i ≠ j →
        w32 t.mem B (arr (kw len) sqD + 4 * i) = w32 x.mem B (arr (kw len) sqD + 4 * i)) →
      pr t.mem B len j = y * 2 ^ 32 + 2 * q →
      (∀ i, i < kw len + 2 → (i < 2 * (j - 1) ∨ 2 * (j - 1) + (wq a - (j - 1) + 3) ≤ i) →
        w32 t.mem B (arr (kw len) sqZ + 4 * i) = w32 x.mem B (arr (kw len) sqZ + 4 * i)) →
      val32 t.mem B (arr (kw len) sqZ + 8 * (j - 1)) (wq a - (j - 1) + 3) = R - (S + q) * q → Qp t) :
    WP isa (.seq (.block VG.Impl.Rsa.X86.RecoverDetRt.updX) (.seq VG.Impl.Rsa.X86.RecoverDetRt.copyBackX
      (.block [.mov .eax (.mem (sc sCt)), .alu .sub .eax (.imm 1), .store (sc sCt) .eax]))) v Qp := by
  have fitD := I.rt.ws.fit64 (j := sqD) (by decide)
  have fitZ := I.rt.ws.fit64 (j := sqZ) (by decide)
  obtain ⟨eZ, eD, eT⟩ := sq_arrs (kw len)
  have hdk : ∀ e ∈ stepDs, e + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr := by decide
  have fD' := fitD; have fZ' := fitZ
  simp only [VG.Proof.Rsa.X86.Keys.S] at fD' fZ'
  have hCv : slot v.mem B sCt = j := (I.keep.slot (e := sCt) (by decide) (by decide)).trans hC
  have hm := I.hm
  refine WP.seq (WP.mono (updX_ok I.rt hm hCv hj1 hj hW) fun v₇ ⟨h₇, O₇, p₇, K₇⟩ => ?_)
  have k₇ : Keep B (kw len) [sqD] [] v.mem v₇.mem :=
    Keep.of_arr (d := 4 * (j - 1)) (n := 8) O₇ (by simp only [VG.Proof.Rsa.X86.Keys.S]; omega_using [hj, hW]) (by simp)
  have hm₇ : MLen v₇ B Z nl a := hm.keep K₇ (by decide) (VG.Proof.Rsa.X86.KeyRt.keep_outside I.rt.ws k₇ (by decide) (by decide))
  have hC₇ : slot v₇.mem B sCt = j := (k₇.slot (e := sCt) (by decide) (by decide)).trans hCv
  refine WP.seq (WP.mono (copyBackX_ok h₇ hm₇ hC₇ hj1 hj hW) fun v₈ ⟨h₈, O₈, z₈, K₈⟩ => ?_)
  have k₈ : Keep B (kw len) [sqZ] [] v₇.mem v₈.mem :=
    Keep.of_arr (d := 8 * (j - 1)) (n := 4 * (wq a - (j - 1) + 3)) O₈ (by simp only [VG.Proof.Rsa.X86.Keys.S]; omega_using [hj, hW2])
      (by simp)
  have hC₈ : slot v₈.mem B sCt = j := (k₈.slot (e := sCt) (by decide) (by decide)).trans hC₇
  refine count_ok h₈ hC₈ hj1 (by simp only [wq] at hj; have := hm.le; omega_using [hj, this]) fun t kt st Kt zt => k t
    (h₈.keep Kt (by decide) (by decide) (VG.Proof.Rsa.X86.KeyRt.keep_outside h₈.ws kt (by decide) (by decide)))
    (I.keeps.trans ((K₇.mono (by decide)).trans ((K₈.mono (by decide)).trans (Kt.mono (by decide)))))
    ((I.keep.mono (by simp) (by simp)).trans ((k₇.mono (by simp) (by simp)).trans
      ((k₈.mono (by simp) (by simp)).trans (kt.mono (by simp) (by simp))))) st zt ?_ ?_ ?_ ?_
  · intro i hi h1 h2
    rw [kt.word (by simp only [VG.Proof.Rsa.X86.Keys.S]; omega_using [hi]) (by simp) (by decide) fitD,
      O₈.w32 (.inl (by rw [eD, eZ]; omega_using [hi])) (by omega_using [fD', hi]), O₇.w32 (by omega_using [hj1, h1, h2]) (by omega_using [fD', hi])]
    exact I.dw i hi h1 h2
  · have p₇' : pr v₇.mem B len j = (pr v.mem B len j + 1) % 2 ^ 64 := p₇
    have e8 : pr t.mem B len j = pr v₇.mem B len j := by
      simp only [pr]
      rw [kt.word (i := j - 1) (by simp only [VG.Proof.Rsa.X86.Keys.S]; omega_using [hj, hW]) (by simp) (by decide) fitD,
        show arr (kw len) sqD + 4 * (j - 1) + 4 = arr (kw len) sqD + 4 * (j - 1 + 1) by omega_using [],
        kt.word (i := j - 1 + 1) (by simp only [VG.Proof.Rsa.X86.Keys.S]; omega_using [hj, hW]) (by simp) (by decide) fitD,
        O₈.w32 (d := arr (kw len) sqD + 4 * (j - 1)) (.inl (by rw [eD, eZ]; omega_using [])) (by omega_using [hj, hW, fD']),
        O₈.w32 (d := arr (kw len) sqD + 4 * (j - 1 + 1)) (.inl (by rw [eD, eZ]; omega_using [])) (by omega_using [hj, hW, fD'])]
    rw [e8, p₇', I.pair]
  · intro i hi hw
    rw [kt.word (by simp only [VG.Proof.Rsa.X86.Keys.S]; omega_using [hi]) (by simp) (by decide) fitZ,
      O₈.w32 (hw.elim (fun hw => .inl (by omega_using [hw])) (fun hw => .inr (by omega_using [hw])))
        (by omega_using [fZ', hi]),
      O₇.w32 (.inr (by rw [eD, eZ]; omega_using [hj, hW])) (by omega_using [fZ', hi])]
    exact I.keep.word (by simp only [VG.Proof.Rsa.X86.Keys.S]; omega_using [hi]) (by decide) hdk fitZ
  · have ht : val32 t.mem B (arr (kw len) sqZ + 8 * (j - 1)) (wq a - (j - 1) + 3) =
        val32 v₈.mem B (arr (kw len) sqZ + 8 * (j - 1)) (wq a - (j - 1) + 3) := by
      rw [show arr (kw len) sqZ + 8 * (j - 1) = arr (kw len) sqZ + 4 * (2 * (j - 1)) by omega_using []]
      exact keep_val32 kt (by simp) (by decide) fitZ (by simp only [VG.Proof.Rsa.X86.Keys.S]; omega_using [hj, hW2])
    rw [ht, z₈, O₇.val32 (.inr (by rw [eD, eT]; omega_using [hj, hW])) (by omega_using [hW, fitZ, eZ, eT]), I.T]
    have hb : (0 : Int) ≤ (R : Int) - ((S + q) * q : Nat) := by omega_using [hq]
    have hW' : ((2 ^ (32 * (wq a - (j - 1) + 3)) : Nat) : Int) / 2 = ((2 ^ (32 * (wq a - (j - 1) + 3)) / 2 : Nat) : Int) := by
      push_cast; rfl
    have := VG.Proof.Bignum.WordStep32.twos_eq (W := 2 ^ (32 * (wq a - (j - 1) + 3)))
      (v := (R : Int) - ((S + q) * q : Nat)) (by omega_using [hq, hWb]) (by omega_using [hWb])
    simp only [show ¬ ((R : Int) - ((S + q) * q : Nat) < 0) by omega_using [hq], ite_false] at this
    omega_using [this]

end

section
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot aM
open VG.Impl.Rsa.X86.RecoverRt (nar wid)
open VG.Impl.Rsa.X86.RecoverDetRt hiding aN aP aQ
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa.X86.KeyRt (RtWs kw)
open VG.Proof.Rsa.X86.WordRt (wq MLen)
open VG.Impl.Rsa.X86.WordModRt (oD oV oQ)

/-- The remainder's window and the next pair: `AW wR = R β^(2 m) + X mod β^(2 m)`, for
`R = r β² + P`. -/
theorem win_split {X r m : Nat} : r * 2 ^ (64 * (m + 1)) + X % 2 ^ (64 * (m + 1)) =
    (r * 2 ^ 64 + X / 2 ^ (64 * m) % 2 ^ 64) * 2 ^ (64 * m) + X % 2 ^ (64 * m) := by
  rw [show 64 * (m + 1) = 64 * m + 64 by omega_using [], Nat.pow_add, Nat.mod_mul]
  obtain ⟨G, eG⟩ : ∃ G, 2 ^ (64 * m) = G := ⟨_, rfl⟩
  rw [eG]
  obtain ⟨H, eH⟩ : ∃ H, (2 : Nat) ^ 64 = H := ⟨_, rfl⟩
  rw [eH]
  grind

/-- `X`'s top part, one pair more. -/
theorem div_pair {X m : Nat} : X / 2 ^ (64 * m) = X / 2 ^ (64 * (m + 1)) * 2 ^ 64 + X / 2 ^ (64 * m) % 2 ^ 64 := by
  rw [show 64 * (m + 1) = 64 * m + 64 by omega_using [], Nat.pow_add, ← Nat.div_div_eq_div_mul]
  exact (Nat.div_add_mod' _ _).symm

end

section
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot aM
open VG.Impl.Rsa.X86.RecoverRt (nar wid)
open VG.Impl.Rsa.X86.RecoverDetRt hiding aN aP aQ
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa.X86.KeyRt (RtWs kw)
open VG.Proof.Rsa.X86.WordRt (wq MLen)
open VG.Impl.Rsa.X86.WordModRt (oD oV oQ)
open VG.Proof.Bignum.SqrtRem (IsDigit)

/-- The numbers of a digit step, at the step's start: `R`'s and `sqD`'s windows. -/
theorem step_windows {m : Mem} {B : Addr} {Wk a j s Zs Xl R : Nat} (hj1 : 1 ≤ j) (hj : j < wq a)
    (hW2 : 2 * wq a + 2 ≤ Wk) (hs : s < 2 ^ (32 * (wq a - j)))
    (hZ : val32 m B (arr Wk sqZ) Wk = Zs) (hZs : Zs = R * 2 ^ (64 * (j - 1)) + Xl) (hXl : Xl < 2 ^ (64 * (j - 1)))
    (hR : R < 2 ^ (32 * (wq a - (j - 1) + 2)))
    (hD : val32 m B (arr Wk sqD) Wk = 2 * s * 2 ^ (32 * j)) :
    val32 m B (arr Wk sqZ + 8 * (j - 1)) (wq a - (j - 1) + 3) = R ∧
      w32 m B (arr Wk sqD + 4 * (j - 1)) = 0 ∧
      w32 m B (arr Wk sqD + 4 * (j - 1) + 4) = 2 * s % 2 ^ 32 ∧
      val32 m B (arr Wk sqD + 4 * (j - 1) + 4) (wq a - (j - 1) + 1) = 2 * s / 2 ^ 32 * 2 ^ 32 + 2 * s % 2 ^ 32 ∧
      val32 m B (arr Wk sqD + 4 * (j - 1) + 8) (wq a - (j - 1) + 1) = 2 * s / 2 ^ 32 := by
  have hs2 : 2 * s < 2 ^ (32 * (wq a - (j - 1) + 1)) := by
    have : 2 ^ (32 * (wq a - j)) * 2 ≤ 2 ^ (32 * (wq a - (j - 1) + 1)) := by
      rw [← Nat.pow_succ]; exact Nat.pow_le_pow_right (by decide) (by omega_using [])
    omega_using [hs, this]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [show arr Wk sqZ + 8 * (j - 1) = arr Wk sqZ + 4 * (2 * (j - 1)) by omega_using [], val32_win _ _ _ _ Wk (by omega_using [hj, hW2]), hZ,
      hZs, show 32 * (2 * (j - 1)) = 64 * (j - 1) by omega_using [], Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
      Nat.div_eq_of_lt hXl, Nat.zero_add, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hR
        (Nat.pow_le_pow_right (by decide) (by omega_using [])))]
  · rw [VG.Proof.Rsa.X86.WordRt.w32_of_val32 m B (n := Wk) (by omega_using [hj, hW2]), hD,
      show 2 ^ (32 * j) = 2 ^ 32 * 2 ^ (32 * (j - 1)) by rw [← Nat.pow_add]; congr 1; omega_using [hj1],
      ← Nat.mul_assoc, Nat.mul_div_cancel _ (Nat.two_pow_pos _), Nat.mul_mod_left]
  · rw [show arr Wk sqD + 4 * (j - 1) + 4 = arr Wk sqD + 4 * j by omega_using [hj1],
      VG.Proof.Rsa.X86.WordRt.w32_of_val32 m B (n := Wk) (by omega_using [hj, hW2]), hD, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
  · rw [show arr Wk sqD + 4 * (j - 1) + 4 = arr Wk sqD + 4 * j by omega_using [hj1], val32_win _ _ _ _ Wk (by omega_using [hj, hW2]), hD,
      Nat.mul_div_cancel _ (Nat.two_pow_pos _), Nat.mod_eq_of_lt hs2]
    exact (Nat.div_add_mod' _ _).symm
  · rw [show arr Wk sqD + 4 * (j - 1) + 8 = arr Wk sqD + 4 * (j + 1) by omega_using [hj1], val32_win _ _ _ _ Wk (by omega_using [hj, hW2]), hD,
      show 2 ^ (32 * (j + 1)) = 2 ^ (32 * j) * 2 ^ 32 by rw [← Nat.pow_add, Nat.mul_add, Nat.mul_one],
      ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hs2)


/-- The half words `estX` reads, at the step's start. -/
theorem step_halves {m : Mem} {B : Addr} {Wk a j s Zs Xl R : Nat} (hj1 : 1 ≤ j) (hj : j < wq a)
    (hW2 : 2 * wq a + 2 ≤ Wk)
    (hZ : val32 m B (arr Wk sqZ) Wk = Zs) (hZs : Zs = R * 2 ^ (64 * (j - 1)) + Xl) (hXl : Xl < 2 ^ (64 * (j - 1)))
    (hD : val32 m B (arr Wk sqD) Wk = 2 * s * 2 ^ (32 * j)) :
    (∀ t, t ≤ 2 → hw m B (arr Wk sqZ) (2 * (j - 1) + (wq a - j - 1 + t)) = wd (R / 2) (wq a - j - 1 + t)) ∧
      hw m B (arr Wk sqD) (j - 1 + (wq a - j - 1)) = wd (s * 2 ^ 32) (wq a - j - 1) := by
  refine ⟨fun t ht => ?_, ?_⟩
  · rw [hw_val m _ _ Wk (by omega_using [hj, hW2, ht]), hZ, wd_shift, Nat.div_div_eq_div_mul, Nat.mul_comm 2, ← Nat.div_div_eq_div_mul,
      hZs, show 32 * (2 * (j - 1)) = 64 * (j - 1) by omega_using [], Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
      Nat.div_eq_of_lt hXl, Nat.zero_add]
  · rw [hw_val m _ _ Wk (by omega_using [hj, hW2]), hD, wd_shift,
      show 2 * s * 2 ^ (32 * j) / 2 = s * 2 ^ 32 * 2 ^ (32 * (j - 1)) by
        rw [show 2 ^ (32 * j) = 2 ^ 32 * 2 ^ (32 * (j - 1)) by rw [← Nat.pow_add]; congr 1; omega_using [hj1],
          Nat.mul_assoc, Nat.mul_div_cancel_left _ (by decide), Nat.mul_assoc],
      Nat.mul_div_cancel _ (Nat.two_pow_pos _)]


theorem step_q5 {q Q : Nat} (h1 : q ≤ Q) (h2 : Q ≤ q + 2) : (if q < Q then Q - 1 else Q) ≤ q + 1 := by
  split <;> omega_arith

theorem step_q6 {q q5 : Nat} (h1 : q ≤ q5) (h2 : q5 ≤ q + 1) : (if q < q5 then q5 - 1 else q5) = q := by
  split <;> omega_arith

/-- After a digit step: the state before the next. -/
theorem step_final {g : Geo} {s0 u t : State} {A V0 AW V : Nat → Nat} {a X j s r q Xl Wk : Nat}
    (h : KS g s0 A [aD, aZero] AW [wR, sqD] V (sCt :: oD :: oV :: lsN) u) (eW : g.W = Wk)
    (hV0 : ∀ d ∈ lsN, V d = V0 d) (hj1 : 1 ≤ j) (hj : j < wq a)
    (hd : V oD = s / 2 ^ (32 * (wq a - 1 - j))) (hd31 : 2 ^ 31 ≤ V oD) (hs : s < 2 ^ (32 * (wq a - j)))
    (hv : V oV = (2 ^ 64 - 1) / V oD - 2 ^ 32) (hr : r ≤ 2 * s) (hsr : s * s + r = X / 2 ^ (64 * j))
    (hq : IsDigit (2 ^ 32) s (r * 2 ^ 64 + X / 2 ^ (64 * (j - 1)) % 2 ^ 64) q)
    (hXl : Xl = X % 2 ^ (64 * (j - 1)))
    (hZ : val32 u.mem g.B (arr Wk sqZ) Wk = (r * 2 ^ 64 + X / 2 ^ (64 * (j - 1)) % 2 ^ 64) * 2 ^ (64 * (j - 1)) + Xl)
    (hD : val32 u.mem g.B (arr Wk sqD) Wk = 2 * s * 2 ^ (32 * j))
    (hZw : val32 u.mem g.B (arr Wk sqZ + 8 * (j - 1)) (wq a - (j - 1) + 3) = r * 2 ^ 64 + X / 2 ^ (64 * (j - 1)) % 2 ^ 64)
    (hD0 : w32 u.mem g.B (arr Wk sqD + 4 * (j - 1)) = 0)
    (hD1 : w32 u.mem g.B (arr Wk sqD + 4 * (j - 1) + 4) = 2 * s % 2 ^ 32)
    (hW2 : 2 * wq a + 2 ≤ Wk)
    (Kt : Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] u t)
    (kt : Keep g.B Wk [sqZ, sqD, sqT] (sCt :: stepDs) u.mem t.mem) (st : slot t.mem g.B sCt = j - 1)
    (dwt : ∀ i, i < Wk + 2 → i ≠ j - 1 → i ≠ j →
      w32 t.mem g.B (arr Wk sqD + 4 * i) = w32 u.mem g.B (arr Wk sqD + 4 * i))
    (pt : w32 t.mem g.B (arr Wk sqD + 4 * (j - 1)) + 2 ^ 32 * w32 t.mem g.B (arr Wk sqD + 4 * (j - 1) + 4) =
      2 * s % 2 ^ 32 * 2 ^ 32 + 2 * q)
    (zwt : ∀ i, i < Wk + 2 → (i < 2 * (j - 1) ∨ 2 * (j - 1) + (wq a - (j - 1) + 3) ≤ i) →
      w32 t.mem g.B (arr Wk sqZ + 4 * i) = w32 u.mem g.B (arr Wk sqZ + 4 * i))
    (zwin : val32 t.mem g.B (arr Wk sqZ + 8 * (j - 1)) (wq a - (j - 1) + 3) =
      r * 2 ^ 64 + X / 2 ^ (64 * (j - 1)) % 2 ^ 64 - (2 * s * 2 ^ 32 + q) * q) :
    SqI g s0 A V0 a X (j - 1) t := by
  obtain ⟨R, eR⟩ : ∃ R, r * 2 ^ 64 + X / 2 ^ (64 * (j - 1)) % 2 ^ 64 = R := ⟨_, rfl⟩
  rw [eR] at hZ hZw zwin
  have hq' := hq
  rw [eR] at hq'
  -- The new `wR` and `sqD`.
  have hZn : val32 t.mem g.B (arr Wk sqZ) Wk = (R - (2 * s * 2 ^ 32 + q) * q) * 2 ^ (64 * (j - 1)) + Xl := by
    have sp := val32_splice (m := u.mem) (m' := t.mem) (B := g.B) (d := arr Wk sqZ) (i := 2 * (j - 1))
      (K := wq a - (j - 1) + 3) (n := Wk) (by omega_using [hj, hW2]) fun k hk hk' => zwt k (by omega_using [hk]) hk'
    rw [show arr Wk sqZ + 4 * (2 * (j - 1)) = arr Wk sqZ + 8 * (j - 1) by omega_using [], hZw, zwin, hZ,
      show 32 * (2 * (j - 1)) = 64 * (j - 1) by omega_using []] at sp
    obtain ⟨G, eG⟩ : ∃ G, 2 ^ (64 * (j - 1)) = G := ⟨_, rfl⟩
    rw [eG] at sp ⊢
    omega_using [sp]
  have hDn : val32 t.mem g.B (arr Wk sqD) Wk = 2 * (s * 2 ^ 32 + q) * 2 ^ (32 * (j - 1)) := by
    have sp := val32_splice (m := u.mem) (m' := t.mem) (B := g.B) (d := arr Wk sqD) (i := j - 1)
      (K := 2) (n := Wk) (by omega_using [hj, hW2]) fun k hk hk' => dwt k (by omega_using [hk]) (by omega_using [hk']) (by omega_using [hk'])
    have e2 : ∀ mm : Mem, val32 mm g.B (arr Wk sqD + 4 * (j - 1)) 2 =
        w32 mm g.B (arr Wk sqD + 4 * (j - 1)) + 2 ^ 32 * w32 mm g.B (arr Wk sqD + 4 * (j - 1) + 4) := fun mm => by
      simp only [val32]; omega_using []
    rw [e2, e2, hD0, hD1, pt, hD, show 2 ^ (32 * j) = 2 ^ 32 * 2 ^ (32 * (j - 1)) by
      rw [← Nat.pow_add]; congr 1; omega_using [hj1]] at sp
    obtain ⟨G, eG⟩ : ∃ G, 2 ^ (32 * (j - 1)) = G := ⟨_, rfl⟩
    rw [eG] at sp ⊢
    obtain ⟨y, ey⟩ : ∃ y, 2 * s % 2 ^ 32 = y := ⟨_, rfl⟩
    rw [ey] at sp
    grind
  -- The KS.
  have kt' : Keep g.B g.W [sqZ, sqD, sqT] (sCt :: stepDs) u.mem t.mem := by rw [eW]; exact kt
  have sep : ∀ d ∈ (sCt :: oD :: oV :: lsN), d ≠ sCt → ∀ e ∈ sCt :: stepDs, d + 4 ≤ e ∨ e + 4 ≤ d := by decide
  have hsl : ∀ d ∈ (sCt :: oD :: oV :: lsN), slot t.mem g.B d = upd V sCt (j - 1) d := by
    intro d hd
    by_cases e : d = sCt
    · subst e; rw [upd_self]; exact st
    · rw [upd_ne _ _ e, ← h.sl d hd]
      exact kt'.slot (h.ls_ok d hd).2.1 (sep d hd e)
  have haW : Arrs t.mem g.B g.W (upd (upd AW wR ((R - (2 * s * 2 ^ 32 + q) * q) * 2 ^ (64 * (j - 1)) + Xl)) sqD
      (2 * (s * 2 ^ 32 + q) * 2 ^ (32 * (j - 1)))) [wR, sqD] := by
    intro jj hjj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hjj
    rcases hjj with rfl | rfl
    · rw [upd_ne _ _ (by decide), upd_self, eW]; exact hZn
    · rw [upd_self, eW]; exact hDn
  have hk : ∀ jj ∈ [sqZ, sqD, sqT], arr g.W jj + S g.W ≤ g.Z := by
    intro jj hjj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hjj
    rcases hjj with rfl | rfl | rfl <;> exact h.wsW.arr_fit (by decide)
  have hKS := h.core kt' hk (by decide) (Kt.mono (by decide)) (h.arrs_W kt' (by decide) (by decide)) h.live_lt
    haW (by decide) hsl h.ls_ok
  -- The root and remainder.
  have eb : (2 : Nat) ^ 32 * 2 ^ 32 = 2 ^ 64 := by rw [← Nat.pow_add]
  have hst := VG.Proof.Bignum.SqrtRem.step_inv (β := 2 ^ 32) (P := X / 2 ^ (64 * (j - 1)) % 2 ^ 64) hsr
    (by rw [eb, eR]; exact hq')
  rw [eb, eR] at hst
  have hdp := div_pair (X := X) (m := j - 1)
  rw [show j - 1 + 1 = j by omega_using [hj1]] at hdp
  have hq32 : q < 2 ^ 32 := VG.Proof.Bignum.SqrtRem.digit_lt (P := X / 2 ^ (64 * (j - 1)) % 2 ^ 64) hr
      (by rw [eb]; exact Nat.mod_lt _ (Nat.two_pow_pos 64)) (by rw [eb, eR]; exact hq'.1)
  have hsj : s * 2 ^ 32 + q < 2 ^ (32 * (wq a - (j - 1))) := by
    rw [show 32 * (wq a - (j - 1)) = 32 * (wq a - j) + 32 by omega_using [hj1, hj], Nat.pow_add]
    have := Nat.mul_le_mul_right (2 ^ 32) (show s + 1 ≤ 2 ^ (32 * (wq a - j)) by omega_using [hs])
    rw [Nat.add_mul, Nat.one_mul] at this
    omega_using [hs, hq32]
  have hdn : (s * 2 ^ 32 + q) / 2 ^ (32 * (wq a - 1 - (j - 1))) = s / 2 ^ (32 * (wq a - 1 - j)) := by
    rw [show 32 * (wq a - 1 - (j - 1)) = 32 + 32 * (wq a - 1 - j) by omega_using [hj1, hj], Nat.pow_add, ← Nat.div_div_eq_div_mul,
      Nat.add_comm, Nat.add_mul_div_right _ _ (by decide), Nat.div_eq_of_lt hq32, Nat.zero_add]
  refine ⟨_, _, s * 2 ^ 32 + q, R - (2 * s * 2 ^ 32 + q) * q, hKS, fun d hd' => ?_, upd_self _ _ _, ?_⟩
  · have nl : ∀ d ∈ lsN, d ≠ sCt := by decide
    rw [upd_ne _ _ (nl d hd'), hV0 d hd']
  have oDn : upd V sCt (j - 1) oD = V oD := upd_ne _ _ (by decide)
  have oVn : upd V sCt (j - 1) oV = V oV := upd_ne _ _ (by decide)
  refine ⟨by rw [upd_self], by rw [upd_ne _ _ (by decide), upd_self, hXl], ?_, ?_, by rw [oDn, hd, hdn], by rw [oDn]; exact hd31,
    hsj, by rw [oVn, oDn]; exact hv⟩
  · rw [hdp]; exact hst.1
  · exact hst.2


/-- `estX` from a digit step's state: the estimate's run (its value aside). -/
theorem estX_sq {g : Geo} {s0 u : State} {A V0 : Nat → Nat} {a X j : Nat}
    (hI : SqI g s0 A V0 a X j u)
    (ha : g.args VG.Impl.Rsa.X86.RecoverDetRt.nl = BitVec.ofNat 32 a) (hal : a ≤ 1024)
    (haw : wq a ≤ g.w) (hj1 : 1 ≤ j) (hj : j < wq a) :
    WP isa (.block VG.Impl.Rsa.X86.RecoverDetRt.estX) u fun v =>
      RtWs wid v g.B g.Z (16 * g.n + 24) 22 ∧
      Keep g.B (kw (16 * g.n + 24)) [] stepDs u.mem v.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] u v := by
  obtain ⟨AW, V, s, r, h, hV0, hVC, hR⟩ := hI
  obtain ⟨hDs, hZs, hsr, hr, hd, hd31, hs, hv⟩ := hR
  have eW : g.W = kw (16 * g.n + 24) := (kw_wid g.n).symm
  have hrt := h.rtW
  have hm := h.mlen ha hal
  have hWw : g.W = 2 * g.w + 2 := rfl
  have hW2 : 2 * wq a + 2 ≤ kw (16 * g.n + 24) := by rw [← eW]; omega_using [haw, hWw]
  have hW : wq a + 3 ≤ kw (16 * g.n + 24) := by omega_using [hj, hW2]
  have hC : slot u.mem g.B sCt = j := (h.sl sCt (by simp)).trans hVC
  have hZ : val32 u.mem g.B (arr (kw (16 * g.n + 24)) sqZ) (kw (16 * g.n + 24)) = AW wR := by
    have := h.arrsW wR (by simp); rw [eW] at this; exact this
  have hD : val32 u.mem g.B (arr (kw (16 * g.n + 24)) sqD) (kw (16 * g.n + 24)) = 2 * s * 2 ^ (32 * j) := by
    have := h.arrsW sqD (by simp); rw [eW] at this; rw [← hDs]; exact this
  -- `R`, the window.
  have ej : j = j - 1 + 1 := by omega_using [hj1]
  have hZ' : val32 u.mem g.B (arr (kw (16 * g.n + 24)) sqZ) (kw (16 * g.n + 24)) =
      (r * 2 ^ 64 + X / 2 ^ (64 * (j - 1)) % 2 ^ 64) * 2 ^ (64 * (j - 1)) + X % 2 ^ (64 * (j - 1)) := by
    rw [hZ, hZs, ej, Nat.add_sub_cancel]; exact win_split
  have hP : X / 2 ^ (64 * (j - 1)) % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (Nat.two_pow_pos 64)
  have hRb : r * 2 ^ 64 + X / 2 ^ (64 * (j - 1)) % 2 ^ 64 < 2 ^ (32 * (wq a - (j - 1) + 2)) := by
    have e : 2 ^ (32 * (wq a - (j - 1) + 2)) = 2 ^ (32 * (wq a - j)) * 2 ^ 96 := by
      rw [← Nat.pow_add]; congr 1; omega_using [hj1, hj]
    rw [e]
    obtain ⟨G, eG⟩ : ∃ G, 2 ^ (32 * (wq a - j)) = G := ⟨_, rfl⟩
    rw [eG] at hs ⊢
    omega_using [hr, hs]
  obtain ⟨hZw, hD0, hD1, hDw, hDh⟩ := step_windows hj1 hj hW2 hs hZ' rfl
    (Nat.mod_lt _ (Nat.two_pow_pos _)) hRb hD
  obtain ⟨hh, hhD⟩ := step_halves hj1 hj hW2 hZ' rfl (Nat.mod_lt _ (Nat.two_pow_pos _)) hD
  -- The estimate.
  have ek : wq a - 1 - j = wq a - j - 1 := by omega_using []
  rw [ek] at hd
  have hs1 : 2 ^ 31 * 2 ^ (32 * (wq a - j - 1)) ≤ s := by
    rw [hd] at hd31; exact (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mp hd31
  have hs2 : s < 2 ^ (32 * (wq a - j - 1 + 1)) := by rw [show wq a - j - 1 + 1 = wq a - j by omega_using [hj]]; exact hs
  obtain ⟨hUD, hU2, hU3, hQq⟩ := est_bounds hs1 hs2 hr hP
  have w3 := words3 ((r * 2 ^ 64 + X / 2 ^ (64 * (j - 1)) % 2 ^ 64) / 2) (wq a - j - 1) hU3
  have t2 := top2_words s (wq a - j - 1)
  rw [← hd] at t2
  have hU : (r * 2 ^ 64 + X / 2 ^ (64 * (j - 1)) % 2 ^ 64) / 2 / 2 ^ (32 * (wq a - j - 1)) =
      hw u.mem g.B (arr (kw (16 * g.n + 24)) sqZ) (wq a + j - 1) * 2 ^ 64 +
        hw u.mem g.B (arr (kw (16 * g.n + 24)) sqZ) (wq a + j - 2) * 2 ^ 32 +
        hw u.mem g.B (arr (kw (16 * g.n + 24)) sqZ) (wq a + j - 3) := by
    rw [show wq a + j - 1 = 2 * (j - 1) + (wq a - j - 1 + 2) by omega_using [hj1, hj], hh 2 (by omega_using []),
      show wq a + j - 2 = 2 * (j - 1) + (wq a - j - 1 + 1) by omega_using [hj1, hj], hh 1 (by omega_using []),
      show wq a + j - 3 = 2 * (j - 1) + (wq a - j - 1 + 0) by omega_using [hj1, hj], hh 0 (by omega_using []), Nat.add_zero (wq a - j - 1), w3]
  have hDd : s * 2 ^ 32 / 2 ^ (32 * (wq a - j - 1)) =
      V oD * 2 ^ 32 + hw u.mem g.B (arr (kw (16 * g.n + 24)) sqD) (wq a - 2) := by
    rw [show wq a - 2 = j - 1 + (wq a - j - 1) by omega_using [hj1, hj], hhD, t2]
  have hud : hw u.mem g.B (arr (kw (16 * g.n + 24)) sqZ) (wq a + j - 1) ≤ V oD := by
    have l0 := Nat.mod_lt ((r * 2 ^ 64 + X / 2 ^ (64 * (j - 1)) % 2 ^ 64) / 2 / 2 ^ (32 * (wq a - j - 1 + 0)))
      (Nat.two_pow_pos 32)
    have l1 := Nat.mod_lt ((r * 2 ^ 64 + X / 2 ^ (64 * (j - 1)) % 2 ^ 64) / 2 / 2 ^ (32 * (wq a - j - 1 + 1)))
      (Nat.two_pow_pos 32)
    have l2 := Nat.mod_lt (s * 2 ^ 32 / 2 ^ (32 * (wq a - j - 1))) (Nat.two_pow_pos 32)
    rw [show wq a + j - 1 = 2 * (j - 1) + (wq a - j - 1 + 2) by omega_using [hj1, hj], hh 2 (by omega_using [])]
    rw [← w3, t2] at hU2
    simp only [wd] at hU2 l0 l1 l2 ⊢
    omega_using [hsr, hr, hd, hd31, hP, hRb, hUD, hU2, hU3, w3, t2, hU, hDd, l0, l1]
  exact WP.mono (estX_ok hrt hm hC hj1 hj hW2 (h.sl oD (by simp))
    ((h.sl oV (by simp)).trans hv) hd31 hU hDd hud hUD) fun v ⟨h₁, k₁, _, K₁⟩ =>
      ⟨h₁, k₁.mono (by simp) (by simp), K₁⟩

/-- A digit step: from the state with `j` digits left to the one with `j - 1`, ZF where none are
left. -/
theorem stepX_ok {g : Geo} {s0 u : State} {A V0 : Nat → Nat} {a X j : Nat}
    (hI : SqI g s0 A V0 a X j u)
    (ha : g.args VG.Impl.Rsa.X86.RecoverDetRt.nl = BitVec.ofNat 32 a) (hal : a ≤ 1024)
    (haw : wq a ≤ g.w) (hj1 : 1 ≤ j) (hj : j < wq a) :
    WP isa VG.Impl.Rsa.X86.RecoverDetRt.stepX u fun v => v.zf = some (decide (j - 1 = 0)) ∧
      SqI g s0 A V0 a X (j - 1) v := by
  obtain ⟨AW, V, s, r, h, hV0, hVC, hR⟩ := hI
  obtain ⟨hDs, hZs, hsr, hr, hd, hd31, hs, hv⟩ := hR
  have eW : g.W = kw (16 * g.n + 24) := (kw_wid g.n).symm
  have hrt := h.rtW
  have hm := h.mlen ha hal
  have hWw : g.W = 2 * g.w + 2 := rfl
  have hW2 : 2 * wq a + 2 ≤ kw (16 * g.n + 24) := by rw [← eW]; omega_using [haw, hWw]
  have hW : wq a + 3 ≤ kw (16 * g.n + 24) := by omega_using [hj, hW2]
  have hC : slot u.mem g.B sCt = j := (h.sl sCt (by simp)).trans hVC
  have hZ : val32 u.mem g.B (arr (kw (16 * g.n + 24)) sqZ) (kw (16 * g.n + 24)) = AW wR := by
    have := h.arrsW wR (by simp); rw [eW] at this; exact this
  have hD : val32 u.mem g.B (arr (kw (16 * g.n + 24)) sqD) (kw (16 * g.n + 24)) = 2 * s * 2 ^ (32 * j) := by
    have := h.arrsW sqD (by simp); rw [eW] at this; rw [← hDs]; exact this
  -- `R`, the window.
  have ej : j = j - 1 + 1 := by omega_using [hj1]
  have hZ' : val32 u.mem g.B (arr (kw (16 * g.n + 24)) sqZ) (kw (16 * g.n + 24)) =
      (r * 2 ^ 64 + X / 2 ^ (64 * (j - 1)) % 2 ^ 64) * 2 ^ (64 * (j - 1)) + X % 2 ^ (64 * (j - 1)) := by
    rw [hZ, hZs, ej, Nat.add_sub_cancel]; exact win_split
  have hP : X / 2 ^ (64 * (j - 1)) % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (Nat.two_pow_pos 64)
  have hRb : r * 2 ^ 64 + X / 2 ^ (64 * (j - 1)) % 2 ^ 64 < 2 ^ (32 * (wq a - (j - 1) + 2)) := by
    have e : 2 ^ (32 * (wq a - (j - 1) + 2)) = 2 ^ (32 * (wq a - j)) * 2 ^ 96 := by
      rw [← Nat.pow_add]; congr 1; omega_using [hj1, hj]
    rw [e]
    obtain ⟨G, eG⟩ : ∃ G, 2 ^ (32 * (wq a - j)) = G := ⟨_, rfl⟩
    rw [eG] at hs ⊢
    omega_using [hr, hs]
  obtain ⟨hZw, hD0, hD1, hDw, hDh⟩ := step_windows hj1 hj hW2 hs hZ' rfl
    (Nat.mod_lt _ (Nat.two_pow_pos _)) hRb hD
  obtain ⟨hh, hhD⟩ := step_halves hj1 hj hW2 hZ' rfl (Nat.mod_lt _ (Nat.two_pow_pos _)) hD
  -- The estimate.
  have ek : wq a - 1 - j = wq a - j - 1 := by omega_using []
  rw [ek] at hd
  have hs1 : 2 ^ 31 * 2 ^ (32 * (wq a - j - 1)) ≤ s := by
    rw [hd] at hd31; exact (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mp hd31
  have hs2 : s < 2 ^ (32 * (wq a - j - 1 + 1)) := by rw [show wq a - j - 1 + 1 = wq a - j by omega_using [hj]]; exact hs
  obtain ⟨hUD, hU2, hU3, hQq⟩ := est_bounds hs1 hs2 hr hP
  obtain ⟨q, hq⟩ := VG.Proof.Bignum.SqrtRem.digit_exists (2 ^ 32) s (r * 2 ^ 64 + X / 2 ^ (64 * (j - 1)) % 2 ^ 64)
  obtain ⟨hQ1, hQ2⟩ := hQq q hq
  have w3 := words3 ((r * 2 ^ 64 + X / 2 ^ (64 * (j - 1)) % 2 ^ 64) / 2) (wq a - j - 1) hU3
  have t2 := top2_words s (wq a - j - 1)
  rw [← hd] at t2
  have hU : (r * 2 ^ 64 + X / 2 ^ (64 * (j - 1)) % 2 ^ 64) / 2 / 2 ^ (32 * (wq a - j - 1)) =
      hw u.mem g.B (arr (kw (16 * g.n + 24)) sqZ) (wq a + j - 1) * 2 ^ 64 +
        hw u.mem g.B (arr (kw (16 * g.n + 24)) sqZ) (wq a + j - 2) * 2 ^ 32 +
        hw u.mem g.B (arr (kw (16 * g.n + 24)) sqZ) (wq a + j - 3) := by
    rw [show wq a + j - 1 = 2 * (j - 1) + (wq a - j - 1 + 2) by omega_using [hj1, hj], hh 2 (by omega_using []),
      show wq a + j - 2 = 2 * (j - 1) + (wq a - j - 1 + 1) by omega_using [hj1, hj], hh 1 (by omega_using []),
      show wq a + j - 3 = 2 * (j - 1) + (wq a - j - 1 + 0) by omega_using [hj1, hj], hh 0 (by omega_using []), Nat.add_zero (wq a - j - 1), w3]
  have hDd : s * 2 ^ 32 / 2 ^ (32 * (wq a - j - 1)) =
      V oD * 2 ^ 32 + hw u.mem g.B (arr (kw (16 * g.n + 24)) sqD) (wq a - 2) := by
    rw [show wq a - 2 = j - 1 + (wq a - j - 1) by omega_using [hj1, hj], hhD, t2]
  have hud : hw u.mem g.B (arr (kw (16 * g.n + 24)) sqZ) (wq a + j - 1) ≤ V oD := by
    have l0 := Nat.mod_lt ((r * 2 ^ 64 + X / 2 ^ (64 * (j - 1)) % 2 ^ 64) / 2 / 2 ^ (32 * (wq a - j - 1 + 0)))
      (Nat.two_pow_pos 32)
    have l1 := Nat.mod_lt ((r * 2 ^ 64 + X / 2 ^ (64 * (j - 1)) % 2 ^ 64) / 2 / 2 ^ (32 * (wq a - j - 1 + 1)))
      (Nat.two_pow_pos 32)
    have l2 := Nat.mod_lt (s * 2 ^ 32 / 2 ^ (32 * (wq a - j - 1))) (Nat.two_pow_pos 32)
    rw [show wq a + j - 1 = 2 * (j - 1) + (wq a - j - 1 + 2) by omega_using [hj1, hj], hh 2 (by omega_using [])]
    rw [← w3, t2] at hU2
    simp only [wd] at hU2 l0 l1 l2 ⊢
    omega_using [hsr, hr, hd, hd31, hP, hRb, hUD, hU2, hU3, hQ1, hQ2, w3, t2, hU, hDd, l0, l1]
  have hQ3 : min ((r * 2 ^ 64 + X / 2 ^ (64 * (j - 1)) % 2 ^ 64) / 2 / 2 ^ (32 * (wq a - j - 1)) /
      (s * 2 ^ 32 / 2 ^ (32 * (wq a - j - 1)))) (2 ^ 32 - 1) < 2 ^ 32 :=
    Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by decide)
  have hWb : r * 2 ^ 64 + X / 2 ^ (64 * (j - 1)) % 2 ^ 64 + 2 * (2 * s * 2 ^ 32) + 4 * q + 4 <
      2 ^ (32 * (wq a - (j - 1) + 3)) / 2 := by
    have eb : (2 : Nat) ^ 32 * 2 ^ 32 = 2 ^ 64 := by rw [← Nat.pow_add]
    have hq32 : q < 2 ^ 32 := VG.Proof.Bignum.SqrtRem.digit_lt hr (by rw [eb]; exact hP)
      (by rw [eb]; exact hq.1)
    have e : 2 ^ (32 * (wq a - (j - 1) + 3)) = 2 ^ (32 * (wq a - j)) * 2 ^ 128 := by
      rw [← Nat.pow_add]; congr 1; omega_using [hj1, hj]
    rw [e]
    obtain ⟨G, eG⟩ : ∃ G, 2 ^ (32 * (wq a - j)) = G := ⟨_, rfl⟩
    rw [eG] at hs ⊢
    omega_using [hs, hr, hP, hq32]
  have hS : 2 * s * 2 ^ 32 = 2 * s / 2 ^ 32 * 2 ^ 64 + 2 * s % 2 ^ 32 * 2 ^ 32 := by omega_using []
  have hy : 2 * s % 2 ^ 32 % 2 = 0 := by omega_using []
  obtain ⟨Q, eQ⟩ : ∃ Q, min ((r * 2 ^ 64 + X / 2 ^ (64 * (j - 1)) % 2 ^ 64) / 2 / 2 ^ (32 * (wq a - j - 1)) /
      (s * 2 ^ 32 / 2 ^ (32 * (wq a - j - 1)))) (2 ^ 32 - 1) = Q := ⟨_, rfl⟩
  rw [eQ] at hQ1 hQ2 hQ3
  -- The run.
  unfold VG.Impl.Rsa.X86.RecoverDetRt.stepX
  simp only [VG.Impl.Rsa.X86.Keys.seqs]
  refine WP.seq (WP.mono (estX_ok hrt hm hC hj1 hj hW2 (h.sl oD (by simp))
    ((h.sl oV (by simp)).trans hv) hd31 hU hDd hud hUD) fun v₁ ⟨h₁, k₁, hQ, K₁⟩ => ?_)
  rw [eQ] at hQ
  have hm₁ := hm.keep K₁ (by decide) (VG.Proof.Rsa.X86.KeyRt.keep_outside hrt.ws k₁ (by decide) (by decide))
  refine pre_ok h₁ hm₁ (k₁.mono (by simp) (by simp)) K₁ hC hQ hj1 hj hW hW2 hZw hD1 hDw hS hy hq hQ1 hQ2 hQ3 hWb
    fun v₄ I₄ => ?_
  refine WP.seq (WP.mono (fix_ok I₄ hC hj1 hj hW hq hWb hDh hS) fun v₅ I₅ => ?_)
  have b₅ := step_q5 hQ1 hQ2
  obtain ⟨q₅, e₅⟩ : ∃ q₅, (if q < Q then Q - 1 else Q) = q₅ := ⟨_, rfl⟩
  rw [e₅] at I₅ b₅
  refine WP.seq (WP.mono (fix_ok I₅ hC hj1 hj hW hq hWb hDh hS) fun v₆ I₆ => ?_)
  rw [step_q6 I₅.q1 b₅] at I₆
  refine WP.seq (WP.mono (fix_ok I₆ hC hj1 hj hW hq hWb hDh hS) fun v₇ I₇ => ?_)
  rw [step_q6 (Nat.le_refl q) (Nat.le_succ q)] at I₇
  refine post_ok I₇ hC hj1 hj hW hW2 hq.1 (by omega_using [hWb]) fun t ht Kt kt st zt dwt pt zwt zwin => ⟨zt, ?_⟩
  have pt' : w32 t.mem g.B (arr (kw (16 * g.n + 24)) sqD + 4 * (j - 1)) +
      2 ^ 32 * w32 t.mem g.B (arr (kw (16 * g.n + 24)) sqD + 4 * (j - 1) + 4) = 2 * s % 2 ^ 32 * 2 ^ 32 + 2 * q := pt
  exact step_final h eW hV0 hj1 hj (by rw [ek]; exact hd) hd31 hs hv hr hsr hq rfl hZ' hD hZw hD0 hD1 hW2 Kt kt st
    dwt pt' zwt zwin

end

end VG.Proof.Rsa.X86.Recover
