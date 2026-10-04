import VerifiedGarbage.Proof.X25519.Edwards.URep
import VerifiedGarbage.Proof.X25519.Ladder
import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# X25519 of the base point is the u-coordinate of a multiple of Ed25519's

RFC 7748 §4.1's birational map `u = (1 + y) / (1 - y)` takes edwards25519's
base point `B` (Ed25519's, RFC 8032 §5.1) to curve25519's, `u = 9`:
`9 (1 - y_B) = 1 + y_B` (`base_u`). The ladder computes, after the bits
`254, …, n` of `k`, the u-coordinates of `[k >> n] B` and `[(k >> n) + 1] B`
(`inv_step`: `URep.dbl` and `URep.dadd`, whose difference is `B`), so
`X25519(k, 9)` is the u-coordinate `(1 + y) / (1 - y)` of `[k] B`
(`x25519_basePoint`), which a fixed-base multiplication on edwards25519 can
compute instead.

The field facts are evaluated by the kernel: `a24 = 121665` is
`-d / (1 + d)`, and `B`'s coordinates are those of RFC 8032.
-/

namespace VG.Proof.X25519.Edwards

open VG.Spec.X25519
open VG.Proof.Ed25519 (toZ_add toZ_sub toZ_mul toZ_one toZ_zero toZ_pow dZ baseAff params)
open VG.Proof.Ed25519.Edwards
open VG.Proof.X25519 (ladderAfter ladderAfter_step ladderAfter_255 ladderAfter_swap_le ladderStep_eq bit
  bit_le x25519_eq toFe leNum leNum_lt leNum_bit getD_set decodeLittleEndian_eq)

/-! ## The field facts -/

private theorem a24_fe : (1 + Spec.Ed25519.d) * a24 = 0 - Spec.Ed25519.d := by decide +kernel

/-- `(1 + d) a24 = -d`: `a24 = (A - 2) / 4` for `A = 2 (1 - d) / (1 + d)`. -/
theorem toZ_a24 : (1 + dZ) * Ed25519.toZ a24 = -dZ := by
  have e := congrArg Ed25519.toZ a24_fe
  rw [toZ_mul, toZ_add, toZ_one, toZ_sub, toZ_zero, zero_sub] at e
  exact e

/-! ## The base point -/

private theorem base_fe : (9 : Fe) * (1 - Spec.Ed25519.basePoint.Y) = 1 + Spec.Ed25519.basePoint.Y := by
  decide +kernel

/-- The base point's u-coordinate is 9. -/
theorem base_u : Ed25519.toZ 9 * (1 - baseAff.y) = 1 + baseAff.y := by
  have e := congrArg Ed25519.toZ base_fe
  rw [toZ_mul, toZ_sub, toZ_add, toZ_one] at e
  exact e

theorem base_x : baseAff.x ≠ 0 := by
  intro h
  have e : Spec.Ed25519.basePoint.X = 0 := Ed25519.toZ_inj.mp (h.trans toZ_zero.symm)
  exact absurd e (by decide +kernel)

theorem nine_ne : Ed25519.toZ 9 ≠ 0 := by
  intro h
  have e : (9 : Fe) = 0 := Ed25519.toZ_inj.mp (h.trans toZ_zero.symm)
  exact absurd e (by decide +kernel)

theorem u_basePoint : toFe (decodeUCoordinate basePoint) = 9 := by decide +kernel

/-! ## The ladder -/

/-- The u-coordinate `(X : Z)` of a pair of field elements is `p`'s. -/
abbrev U (a : Fe × Fe) (p : EPoint dZ) : Prop := URep (Ed25519.toZ a.1) (Ed25519.toZ a.2) p

/-- The ladder's state after the bits `254, …, n` of `k`: once swapped by
`swap`, the u-coordinates of `[k >> n] B` and `[(k >> n) + 1] B`. -/
def Inv (k n : Nat) (st : Ladder) : Prop :=
  U ((cswap st.swap st.x2 st.x3).1, (cswap st.swap st.z2 st.z3).1) ((k >>> n) • baseAff) ∧
    U ((cswap st.swap st.x2 st.x3).2, (cswap st.swap st.z2 st.z3).2) ((k >>> n + 1) • baseAff)

theorem dbl {x z : Fe} {p : EPoint dZ} (h : U (x, z) p) :
    U ((x + z) * (x + z) * ((x - z) * (x - z)),
      ((x + z) * (x + z) - (x - z) * (x - z)) *
        ((x + z) * (x + z) + a24 * ((x + z) * (x + z) - (x - z) * (x - z)))) (p + p) := by
  have := h.dbl toZ_a24
  simp only [U, toZ_mul, toZ_add, toZ_sub] at this ⊢
  exact this

theorem dadd {x2 z2 x3 z3 : Fe} {p q : EPoint dZ} (h2 : U (x2, z2) p) (h3 : U (x3, z3) q)
    (hb : q - p = baseAff ∨ p - q = baseAff) :
    U (((x3 - z3) * (x2 + z2) + (x3 + z3) * (x2 - z2)) * ((x3 - z3) * (x2 + z2) + (x3 + z3) * (x2 - z2)),
      9 * (((x3 - z3) * (x2 + z2) - (x3 + z3) * (x2 - z2)) *
        ((x3 - z3) * (x2 + z2) - (x3 + z3) * (x2 - z2)))) (p + q) := by
  have := h2.dadd h3 hb base_x base_u nine_ne
  simp only [U, toZ_mul, toZ_add, toZ_sub] at this ⊢
  exact this

/-- One iteration keeps `Inv`, for bit `n` of the scalar. -/
theorem inv_step (k n : Nat) (st : Ladder) (hs : st.swap ≤ 1) (h : Inv k (n + 1) st) :
    Inv k n (ladderStep k 9 st n) := by
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

theorem inv_init (k : Nat) (h0 : k >>> 255 = 0) : Inv k 255 (VG.Proof.X25519.init 9) := by
  simp only [Inv, VG.Proof.X25519.init, cswap, h0, zero_nsmul, zero_add, one_nsmul, Nat.reduceEqDiff,
    ↓reduceIte]
  refine ⟨⟨?_, Or.inl ?_⟩, ⟨?_, Or.inr ?_⟩⟩
  · rw [toZ_one, toZ_zero, zero_y]; ring
  · rw [toZ_one]; exact one_ne_zero
  · rw [toZ_one, one_mul]; exact base_u
  · rw [toZ_one]; exact one_ne_zero

theorem inv_after (k : Nat) (hk : k >>> 255 = 0) :
    ∀ j ≤ 255, Inv k (255 - j) (ladderAfter k 9 (255 - j)) := by
  intro j
  induction j with
  | zero => intro _; rw [ladderAfter_255]; exact inv_init k hk
  | succ j ih =>
    intro hj
    have hn : 255 - (j + 1) < 255 := by omega
    rw [ladderAfter_step k 9 hn]
    have e : 255 - (j + 1) + 1 = 255 - j := by omega
    refine inv_step k _ _ ?_ ?_
    · rw [e]; exact ladderAfter_swap_le k 9 (by omega)
    · rw [e]; exact ih (by omega)

/-- Bit 7 of a byte masked with `127` and then 64 set is clear. -/
private theorem bit7_and_or_64 : ∀ x < 256, (((x &&& 127) ||| 64) >>> 7) &&& 1 = 0 := by
  decide +kernel

/-- The decoded scalar of 32 bytes has 255 bits (bit 255 is cleared). -/
theorem decodeScalar25519_shift {kb : List Byte} (h : kb.length = 32) :
    decodeScalar25519 kb >>> 255 = 0 := by
  have hlt : decodeScalar25519 kb < 2 ^ 256 := by
    simp only [decodeScalar25519, decodeLittleEndian_eq]
    refine Nat.lt_of_lt_of_le (leNum_lt _) ?_
    rw [show (2 : Nat) ^ 256 = 256 ^ 32 by norm_num]
    exact Nat.pow_le_pow_right (by decide) (List.length_take_le _ _)
  have hbit : (decodeScalar25519 kb >>> 255) &&& 1 = 0 := by
    simp only [decodeScalar25519, decodeLittleEndian_eq]
    rw [List.take_of_length_le (by simp [h]), leNum_bit,
      getD_set _ _ _ (by simp [h]), getD_set _ _ _ (by simp [h])]
    simp only [show 255 / 8 = 31 by rfl, show 255 % 8 = 7 by rfl, ↓reduceIte]
    rw [BitVec.toNat_or, BitVec.toNat_and, show (127 : BitVec 8).toNat = 127 from rfl,
      show (64 : BitVec 8).toNat = 64 from rfl]
    exact bit7_and_or_64 _ (BitVec.isLt _)
  have h2 : decodeScalar25519 kb >>> 255 < 2 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_lt_of_lt_mul (by rw [← Nat.pow_succ]; exact hlt)
  rw [Nat.and_one_is_mod] at hbit
  omega

/-- `z^(P-2) = z⁻¹`, also for `z = 0`. -/
theorem pow_P_sub_two (z : ZMod P) : z ^ (P - 2) = z⁻¹ := by
  by_cases hz : z = 0
  · rw [hz, inv_zero, zero_pow (by decide +kernel)]
  · refine (eq_inv_of_mul_eq_one_left ?_)
    rw [← pow_succ, show P - 2 + 1 = P - 1 by decide +kernel, ZMod.pow_card_sub_one_eq_one hz]

/-- **X25519 of the base point** is the u-coordinate `(1 + y) / (1 - y)`
(with `(1 + y) / 0 = 0`) of `[k] B` on edwards25519, for the decoded scalar
`k` of a 32-byte string. -/
theorem x25519_basePoint {kb : List Byte} (hk : kb.length = 32) (w : Fe)
    (hw : Ed25519.toZ w = (1 + ((decodeScalar25519 kb) • baseAff).y) / (1 - ((decodeScalar25519 kb) • baseAff).y)) :
    x25519 kb basePoint = encodeUCoordinate w := by
  rw [x25519_eq, u_basePoint]
  simp only
  refine congrArg encodeUCoordinate (Ed25519.toZ_inj.mp ?_)
  have h := (inv_after (decodeScalar25519 kb) (decodeScalar25519_shift hk) 255 le_rfl).1
  rw [Nat.sub_self, Nat.shiftRight_zero] at h
  rw [hw, ← h.out params, toZ_mul, VG.Proof.X25519.invert_eq, toZ_pow, pow_P_sub_two]

end VG.Proof.X25519.Edwards
