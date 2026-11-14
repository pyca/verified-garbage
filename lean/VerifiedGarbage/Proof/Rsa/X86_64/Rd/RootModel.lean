module

public import VerifiedGarbage.Proof.Rsa.RecoverDetModel
import VerifiedGarbage.Proof.Rsa.RecoverDetWords
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Data.Nat.GCD.Basic

-- separate module: the model's root by words, apart from the code's proofs

/-!
# `vg_rsa_recover_primes_det` on x86-64: the model's root as `isqrt`

`aOf_closed`: the model's `a`. `model_correct_c`: `model_correct` with the
quotient needed only where `d e ≥ 2` and `m < n`. The square root by words computes `isqrt` of `b² - 4 n` reduced to the low
words that hold it, and whether that is a square. Where the earlier checks
pass (`m < n`, the quotient `q` of `n - r` by `m + 1`, and `b² > 4 n`), so
that `b ≤ n + 1`, the model's bit-serial root (`rootOf`) is that root, and its
remainder is zero exactly where `b² - 4 n` is a square (the shared `root_bridge`,
`Proof/Rsa/RecoverRoot.lean`); `xOf_lt`: that `b² - 4 n` fits the words that hold it.
-/

@[expose] public section

namespace VG.Proof.Rsa.RecoverDet

open VG.Spec.Rsa (isqrt)

/-- Where the shared `root_bridge` applies, `X = b² - 4 n` is below `(n + 1)²`, so the code's reduction of
`X` to its low words keeps it. -/
theorem xOf_lt {nb wb n de q P : Nat} (three : 3 ≤ n) (hn : 8 * (n + 2) ≤ 2 ^ nb) (hw : 2 * nb ≤ wb)
    (hP : (n + 1) * (n + 1) ≤ P) (hlt : ltOf nb wb n de = true)
    (hq : q = dOf nb wb n de / m1Of nb wb n de) (h4 : ok4Of nb wb n (bOf nb q) = true) :
    xOf nb wb n (bOf nb q) < P := by
  have pnb : 2 ^ nb ≤ 2 ^ wb := Nat.pow_le_pow_right (by decide) (by omega_using [hw])
  have p2 : 2 ^ nb * 2 ^ nb ≤ 2 ^ wb := by rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega_using [hw])
  have rlt : rOf nb wb n de < n := Nat.mod_lt _ (by omega_using [three])
  have dv : dOf nb wb n de = n - rOf nb wb n de := by
    unfold dOf; rw [Nat.mod_eq_of_lt (by omega_using [hn, rlt]), wsub_of_le (by omega_using [hn]) (by omega_using [rlt])]
  have mlt : mOf nb wb n de < n := by simpa [ltOf] using hlt
  have m1 : m1Of nb wb n de = mOf nb wb n de + 1 := by
    unfold m1Of; rw [Nat.mod_eq_of_lt (a := mOf nb wb n de) (by omega_using [hn, mlt]), Nat.mod_eq_of_lt (by omega_using [hn, mlt])]
  have qle : q ≤ n := by rw [hq, dv, m1]; exact Nat.le_trans (Nat.div_le_self _ _) (by omega_using [])
  have hb : bOf nb q = q + 1 := by unfold bOf; exact Nat.mod_eq_of_lt (by omega_using [hn, qle])
  rw [hb] at h4 ⊢
  have hb1 : q + 1 ≤ n + 1 := by omega_using [qle]
  generalize q + 1 = b at *
  have blt : b < 2 ^ nb := by omega_using [hn, hb1]
  have bb : b * b < 2 ^ wb := Nat.lt_of_lt_of_le (Nat.mul_lt_mul'' blt blt) p2
  have sq : sqOf nb wb b = b * b := by
    unfold sqOf; rw [prod_iter _ _ _ (by omega_using [hn, pnb, hb1])]; simp only
    rw [Nat.mod_eq_of_lt blt, Nat.mod_eq_of_lt bb]
  have f4 : fourN wb n = 4 * n := by
    unfold fourN
    rw [Nat.mod_eq_of_lt (a := 2 * n) (by omega_using [three, hn, hP, hq, pnb, p2, rlt, dv, mlt, m1, qle, hb1, blt, bb]), Nat.mod_eq_of_lt (by omega_using [three, hn, hP, hq, pnb, p2, rlt, dv, mlt, m1, qle, hb1, blt, bb])]; grind
  have big : ¬ (b * b < 4 * n) ∧ ¬ (xOf nb wb n b < 1) := by
    unfold ok4Of at h4; rw [sq, f4] at h4; simpa using h4
  have xv : xOf nb wb n b = b * b - 4 * n := by
    unfold xOf; rw [sq, f4, wsub_of_le bb (by omega_using [big])]
  have hbn : b * b ≤ (n + 1) * (n + 1) := Nat.mul_self_le_mul_self (by omega_using [hb1])
  rw [xv]
  omega_using [three, hP, big, hbn]

/-- The model's `a` in closed form, for `2 ≤ d e < 2^nb`. -/
theorem aOf_closed {nb wb n de : Nat} (three : 3 ≤ n) (hn : 8 * (n + 2) ≤ 2 ^ nb) (hw : 2 * nb ≤ wb)
    (hde2 : 2 ≤ de) (hde : de < 2 ^ nb) :
    aOf nb wb n de = (de - 1) * Nat.gcd (n - 1) (de - 1) := by
  have p2 : 2 ^ nb * 2 ^ nb ≤ 2 ^ wb := by rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega_using [hw])
  have pnb : 2 ^ nb ≤ 2 ^ wb := Nat.pow_le_pow_right (by decide) (by omega_using [hw])
  have dx : deX wb de = de - 1 := wsub_of_le (by omega) (by omega_using [hde2])
  have xlt : de - 1 < 2 ^ nb := by omega_using [hde]
  have un : wsub nb n 1 = n - 1 := wsub_of_le (by omega_using [hn]) (by omega_using [three])
  obtain ⟨uodd, ule, g, hx2, hx3, hgcd⟩ :=
    twos_iter (b := wb) (N := n - 1) (x := de - 1) (k := nb) (by omega_using [three]) (by omega_using [hn]) (by omega_using [hde, pnb])
  have tw : twosOut nb wb n de = (twoStep wb)^[nb] (n - 1, de - 1, de - 1) := by
    unfold twosOut; rw [un, dx, Nat.mod_eq_of_lt xlt]
  generalize (twoStep wb)^[nb] (n - 1, de - 1, de - 1) = s at tw uodd ule hx2 hx3 hgcd
  obtain ⟨u, x2, x3⟩ := s
  simp only at uodd ule hx2 hx3 hgcd
  have g_le : g ≤ Nat.gcd (n - 1) (de - 1) := by
    rw [hgcd]; exact Nat.le_mul_of_pos_right _ (Nat.gcd_pos_of_pos_left _ (by omega_using [uodd]))
  have gle : Nat.gcd (n - 1) (de - 1) ≤ n - 1 := Nat.gcd_le_left _ (by omega_using [three])
  have big : (de - 1) * Nat.gcd (n - 1) (de - 1) < 2 ^ wb := by
    calc (de - 1) * Nat.gcd (n - 1) (de - 1) < 2 ^ nb * 2 ^ nb :=
          Nat.mul_lt_mul'' xlt (by omega_using [hn, gle])
      _ ≤ 2 ^ wb := p2
  have x3v : x3 = (de - 1) * g := by
    rw [hx3]; exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ g_le) big)
  have g1le : Nat.gcd u x2 ≤ n - 1 := Nat.le_trans (Nat.gcd_le_left _ (by omega_using [uodd])) ule
  unfold aOf
  rw [tw, prod_iter _ _ _ (by rw [x3v]; exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ g_le) big)]
  simp only
  rw [Nat.mod_eq_of_lt (show Nat.gcd u x2 < 2 ^ nb by omega_using [hn, g1le]), x3v, hgcd]
  rw [Nat.mod_eq_of_lt (by rw [hgcd] at big; simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] at big ⊢; exact big)]
  grind

/-- `model_correct`, with the division's quotient and remainder only where `d e ≥ 2`
and `m < n`. -/
theorem model_correct_c {nb wb n e d q rem : Nat} (odd : n % 2 = 1) (three : 3 ≤ n)
    (hn : 8 * (n + 2) ≤ 2 ^ nb) (hde : d * e < 2 ^ nb) (hw : 2 * nb ≤ wb) (hwe : wb % 2 = 0)
    (hdiv : okDE wb (d * e) = true → ltOf nb wb n (d * e) = true →
      q = dOf nb wb n (d * e) / m1Of nb wb n (d * e) ∧ rem = dOf nb wb n (d * e) % m1Of nb wb n (d * e)) :
    result nb wb n (d * e) q rem = VG.Spec.Rsa.recoverDet n e d := by
  by_cases hk : okDE wb (d * e) = true
  · exact model_correct_lt odd three hn hde hw hwe fun hl _ => hdiv hk hl
  · have hk' : okDE wb (d * e) = false := by simpa using hk
    rw [← model_correct (q := dOf nb wb n (d * e) / m1Of nb wb n (d * e))
      (rem := dOf nb wb n (d * e) % m1Of nb wb n (d * e)) odd three hn hde hw hwe fun _ => ⟨rfl, rfl⟩]
    simp [result, hk']

end VG.Proof.Rsa.RecoverDet
