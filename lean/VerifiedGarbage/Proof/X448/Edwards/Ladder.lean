import VerifiedGarbage.Proof.X448.Edwards.URep
import VerifiedGarbage.Proof.Ed448.Group.Projective
import VerifiedGarbage.Proof.X448.Bytes
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# X448 of the base point is the u-coordinate of a multiple of Ed448's

RFC 7748 §4.2's 4-isogeny `u = y² / x²` takes edwards448's base point `B`
(Ed448's, RFC 8032 §5.2) to curve448's, `u = 5`: `5 x_B² = y_B²` (`base_u`).
The ladder computes, after the bits `447, …, n` of `k`, the u-coordinates of
`[k >> n] B` and `[(k >> n) + 1] B` (`inv_step`: `URep.dbl` and `URep.dadd`,
whose difference is `B`), so `X448(k, 5)` is the u-coordinate `y² / x²` of
`[k] B` (`x448_basePoint`), which a fixed-base multiplication on edwards448
can compute instead.

The field facts are evaluated by the kernel: `1 - d = 39082` is not a square
(its power `(P - 1) / 2` is `-1`, as for `d` in `Ed448/Group/Projective.lean`),
and `a24 = -d`.
-/

namespace VG.Proof.X448.Edwards

open VG.Spec.X448
open VG.Proof.Ed448 (toZ_add toZ_sub toZ_mul toZ_one toZ_zero toZ_inj toZ_ne_zero toZ_pow toZ_neg
  dZ baseAff PZ PZ_eq pow_P_sub_one two_ne_zero')
open VG.Proof.Ed448.Edwards
open VG.Proof.X448 (ladderAfter ladderAfter_step ladderAfter_448 ladderAfter_swap_le ladderStep_eq bit
  bit_le x448_eq toFe)

/-! ## The field facts -/

private theorem one_sub_d_pow : Pratt.powMod PZ 449 39082 ((P - 1) / 2) = PZ - 1 := by
  decide +kernel

theorem one_sub_dZ : (1 : ZMod PZ) - dZ = ((39082 : Nat) : ZMod PZ) := by
  rw [dZ, show Spec.Ed448.d = 0 - 39081 from rfl, toZ_neg, sub_neg_eq_add]
  rw [show (39081 : Fe) = toFe 39081 from rfl]
  unfold Ed448.toZ toFe
  rw [Fin.val_ofNat, Nat.mod_eq_of_lt (by decide +kernel)]
  push_cast; ring

theorem one_sub_dZ_pow : (1 - dZ) ^ ((P - 1) / 2) = -1 := by
  rw [one_sub_dZ, ← Pratt.powMod_cast PZ 449 _ _ (by decide +kernel), one_sub_d_pow,
    Nat.cast_sub (by decide +kernel), ZMod.natCast_self, Nat.cast_one, zero_sub]

/-- `1 - d` is not a square in `ZMod PZ`. -/
theorem one_sub_dZ_nonsq (r : ZMod PZ) : r ^ 2 ≠ 1 - dZ := by
  intro hr
  have hr0 : r ≠ 0 := by
    rintro rfl
    have h := one_sub_dZ_pow
    rw [← hr, zero_pow (by decide), zero_pow (by decide +kernel)] at h
    exact one_ne_zero (neg_eq_zero.mp h.symm)
  have h2 := one_sub_dZ_pow
  rw [← hr, ← pow_mul, show 2 * ((P - 1) / 2) = P - 1 by decide +kernel, pow_P_sub_one hr0] at h2
  exact two_ne_zero' (by linear_combination h2)

theorem toZ_a24 : Ed448.toZ a24 = -dZ := by
  rw [dZ, show Spec.Ed448.d = 0 - a24 from rfl, toZ_neg, neg_neg]

/-! ## The base point -/

private theorem base_fe : (5 : Fe) * (Spec.Ed448.basePoint.X * Spec.Ed448.basePoint.X) =
    Spec.Ed448.basePoint.Y * Spec.Ed448.basePoint.Y := by decide +kernel

/-- The base point's u-coordinate is 5. -/
theorem base_u : Ed448.toZ 5 * baseAff.x ^ 2 = baseAff.y ^ 2 := by
  have e := congrArg Ed448.toZ base_fe
  simp only [toZ_mul] at e
  simp only [baseAff, sq]
  exact e

theorem base_x : baseAff.x ≠ 0 :=
  toZ_ne_zero.mpr (by decide +kernel)

theorem five_ne : Ed448.toZ 5 ≠ 0 :=
  toZ_ne_zero.mpr (by decide +kernel)

theorem u_basePoint : toFe (decodeUCoordinate basePoint) = 5 := by decide +kernel

/-! ## The ladder -/

/-- The u-coordinate `(X : Z)` of a pair of field elements is `p`'s. -/
abbrev U (a : Fe × Fe) (p : EPoint dZ) : Prop := URep (Ed448.toZ a.1) (Ed448.toZ a.2) p

/-- The ladder's state after the bits `447, …, n` of `k`: once swapped by
`swap`, the u-coordinates of `[k >> n] B` and `[(k >> n) + 1] B`. -/
def Inv (k n : Nat) (st : Ladder) : Prop :=
  U ((cswap st.swap st.x2 st.x3).1, (cswap st.swap st.z2 st.z3).1) ((k >>> n) • baseAff) ∧
    U ((cswap st.swap st.x2 st.x3).2, (cswap st.swap st.z2 st.z3).2) ((k >>> n + 1) • baseAff)

theorem dbl {x z : Fe} {p : EPoint dZ} (h : U (x, z) p) :
    U ((x + z) * (x + z) * ((x - z) * (x - z)),
      ((x + z) * (x + z) - (x - z) * (x - z)) *
        ((x + z) * (x + z) + a24 * ((x + z) * (x + z) - (x - z) * (x - z)))) (p + p) := by
  have := h.dbl one_sub_dZ_nonsq
  simp only [U, toZ_mul, toZ_add, toZ_sub, toZ_a24] at this ⊢
  exact this

theorem dadd {x2 z2 x3 z3 : Fe} {p q : EPoint dZ} (h2 : U (x2, z2) p) (h3 : U (x3, z3) q)
    (hb : q - p = baseAff ∨ p - q = baseAff) :
    U (((x3 - z3) * (x2 + z2) + (x3 + z3) * (x2 - z2)) * ((x3 - z3) * (x2 + z2) + (x3 + z3) * (x2 - z2)),
      5 * (((x3 - z3) * (x2 + z2) - (x3 + z3) * (x2 - z2)) *
        ((x3 - z3) * (x2 + z2) - (x3 + z3) * (x2 - z2)))) (p + q) := by
  have := h2.dadd one_sub_dZ_nonsq h3 hb base_x base_u five_ne
  simp only [U, toZ_mul, toZ_add, toZ_sub] at this ⊢
  exact this

/-- One iteration keeps `Inv`, for bit `n` of the scalar. -/
theorem inv_step (k n : Nat) (st : Ladder) (hs : st.swap ≤ 1) (h : Inv k (n + 1) st) :
    Inv k n (ladderStep k 5 st n) := by
  have hm : k >>> n = 2 * (k >>> (n + 1)) + bit k n := by
    simp only [bit, Nat.shiftRight_succ, Nat.and_one_is_mod]; omega
  set m := k >>> (n + 1)
  obtain ⟨h0, h1⟩ := h
  rw [ladderStep_eq]
  have hb := bit_le k n
  -- The swap applied in the step is the stored one, then the bit's.
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hs with hs0 | hs1 <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with hb0 | hb1
  · simp only [hs0, hb0, cswap, Nat.xor_self, Nat.reduceEqDiff, ↓reduceIte] at h0 h1 ⊢
    refine ⟨?_, ?_⟩
    · rw [hm, hb0, Nat.add_zero, two_mul, add_nsmul]; exact dbl h0
    · rw [hm, hb0, Nat.add_zero, show 2 * m + 1 = m + (m + 1) by omega, add_nsmul]
      exact dadd h0 h1 (Or.inl (by rw [add_nsmul, one_nsmul, add_sub_cancel_left]))
  · simp only [hs0, hb1, cswap, Nat.zero_xor, ↓reduceIte] at h0 h1 ⊢
    refine ⟨?_, ?_⟩
    · rw [hm, hb1, show 2 * m + 1 = (m + 1) + m by omega, add_nsmul]
      exact dadd h1 h0 (Or.inr (by rw [add_nsmul, one_nsmul, add_sub_cancel_left]))
    · rw [hm, hb1, show 2 * m + 1 + 1 = (m + 1) + (m + 1) by omega, add_nsmul]; exact dbl h1
  · simp only [hs1, hb0, cswap, Nat.xor_zero, ↓reduceIte] at h0 h1 ⊢
    refine ⟨?_, ?_⟩
    · rw [hm, hb0, Nat.add_zero, two_mul, add_nsmul]; exact dbl h0
    · rw [hm, hb0, Nat.add_zero, show 2 * m + 1 = m + (m + 1) by omega, add_nsmul]
      exact dadd h0 h1 (Or.inl (by rw [add_nsmul, one_nsmul, add_sub_cancel_left]))
  · simp only [hs1, hb1, cswap, Nat.xor_self, ↓reduceIte] at h0 h1 ⊢
    refine ⟨?_, ?_⟩
    · rw [hm, hb1, show 2 * m + 1 = (m + 1) + m by omega, add_nsmul]
      exact dadd h1 h0 (Or.inr (by rw [add_nsmul, one_nsmul, add_sub_cancel_left]))
    · rw [hm, hb1, show 2 * m + 1 + 1 = (m + 1) + (m + 1) by omega, add_nsmul]; exact dbl h1

theorem inv_init (k : Nat) (h0 : k >>> 448 = 0) : Inv k 448 (VG.Proof.X448.init 5) := by
  simp only [Inv, VG.Proof.X448.init, cswap, h0, zero_nsmul, zero_add, one_nsmul, Nat.reduceEqDiff,
    ↓reduceIte]
  refine ⟨⟨?_, Or.inl ?_⟩, ⟨?_, Or.inr ?_⟩⟩
  · rw [toZ_one, toZ_zero, zero_x, zero_y]; ring
  · rw [toZ_one]; exact one_ne_zero
  · simp only [toZ_one, one_mul]; exact base_u
  · rw [toZ_one]; exact one_ne_zero

theorem inv_after (k : Nat) (hk : k >>> 448 = 0) :
    ∀ j ≤ 448, Inv k (448 - j) (ladderAfter k 5 (448 - j)) := by
  intro j
  induction j with
  | zero => intro _; rw [ladderAfter_448]; exact inv_init k hk
  | succ j ih =>
    intro hj
    have hn : 448 - (j + 1) < 448 := by omega
    rw [ladderAfter_step k 5 hn]
    have e : 448 - (j + 1) + 1 = 448 - j := by omega
    refine inv_step k _ _ ?_ ?_
    · rw [e]; exact ladderAfter_swap_le k 5 (by omega)
    · rw [e]; exact ih (by omega)

theorem shiftRight_of_lt {x n : Nat} (h : x < 256 ^ n) : x >>> (8 * n) = 0 := by
  rw [Nat.shiftRight_eq_div_pow, Nat.pow_mul]; exact Nat.div_eq_of_lt h

/-- The decoded scalar has 448 bits. -/
theorem decodeScalar448_shift (kb : List Byte) : decodeScalar448 kb >>> 448 = 0 := by
  rw [decodeScalar448, VG.Proof.X448.decodeLittleEndian_eq]
  exact shiftRight_of_lt (n := 56) (Nat.lt_of_lt_of_le (VG.Proof.X25519.leNum_lt _)
    (Nat.pow_le_pow_right (by decide) (List.length_take_le _ _)))

/-- `z^(P-2) = z⁻¹`, also for `z = 0`. -/
theorem pow_P_sub_two (z : ZMod PZ) : z ^ (P - 2) = z⁻¹ := by
  by_cases hz : z = 0
  · rw [hz, inv_zero, zero_pow (by decide +kernel)]
  · refine (eq_inv_of_mul_eq_one_left ?_)
    rw [← pow_succ, show P - 2 + 1 = P - 1 by decide +kernel, pow_P_sub_one hz]

/-- **X448 of the base point** is the u-coordinate `y² / x²` (with `y² / 0 =
0`) of `[k] B` on edwards448, for the decoded scalar `k`. -/
theorem x448_basePoint (kb : List Byte) (w : Fe)
    (hw : Ed448.toZ w = ((decodeScalar448 kb) • baseAff).y ^ 2 / ((decodeScalar448 kb) • baseAff).x ^ 2) :
    x448 kb basePoint = encodeUCoordinate w := by
  rw [x448_eq, u_basePoint]
  simp only
  refine congrArg encodeUCoordinate (Ed448.toZ_inj.mp ?_)
  have h := (inv_after (decodeScalar448 kb) (decodeScalar448_shift kb) 448 le_rfl).1
  rw [Nat.sub_self, Nat.shiftRight_zero] at h
  rw [hw, ← h.out, toZ_mul, VG.Proof.X448.invert_eq, toZ_pow, pow_P_sub_two]

end VG.Proof.X448.Edwards
