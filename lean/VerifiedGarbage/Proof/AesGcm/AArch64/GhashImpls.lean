module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Callee
public import VerifiedGarbage.Proof.Gcm.AArch64.Holes
public import VerifiedGarbage.Proof.Gcm.AArch64.Pmull.Ghash
public import VerifiedGarbage.Proof.Gcm.AArch64.Neon.Ghash
import VerifiedGarbage.Proof.Gcm.AArch64.Lit
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Ops

/-!
# AES-GCM on AArch64: `vg_ghash`, `vg_ghash_aes`, `vg_ghash_prepared8_aes` and `vg_ghash_with_powers_aes`

Untrusted: everything here is checked by Lean. The `GhashImpl`s of
`vg_ghash` and `vg_ghash_aes` and the `GhashPreparedImpl` of
`vg_ghash_prepared8_aes`, from their proofs, apart from `Callee.lean`: only
the variants need them, and their proofs import the algebra of
`Proof/Gcm/Poly.lean`, which the rest of the AES-GCM proofs then need not
import. So does `gh8Ok`, which
the interleaved loops' proofs (`Proof/Gcm/AArch64/Stitch/`) take as a
hypothesis: what `ghPart` computes (`gh8V`) is GHASH of its eight blocks, in
the ring `Q` of `Proof/Gcm/Poly.lean`. Karatsuba's products (`kadd`) add
`x · a · s` once `fix`ed (`val_fix_kadd`): `mid` has the two products
`vg_ghash_aes` adds to it, and the other two each twice. The power `H'ᵏ` with
its halves swapped is of the class of `x⁻¹ · Hᵏ` (`x_φ_pp`).
-/

@[expose] public section


local notation "vdword" => VG.Proof.Gcm.Clmul.vdword
local notation "ofVDwords" => VG.Proof.Gcm.Clmul.ofVDwords

/-! ## `vg_ghash_neon`: the arithmetic

What `Proof/Gcm/AArch64/Neon/Ghash.lean` takes as a hypothesis (`Arith`):
`pmull` of eight pairs of bytes (`pmB`) multiplies polynomials lane by lane,
and fifteen of them, of the two factors shifted by whole bytes in opposite
directions, add up to the product of two doublewords (`cl_polyMul`); the
reduction by shifts is of the class of the product (`ρ_reduceN`), so that a
block's instructions compute `mulV` (`mulN_eq`); and `twist` computes
`vg_ghash_aes`'s key (`twistV_key`). -/

namespace VG.Proof.Gcm.AArch64.Neon

open Polynomial
open VG.AArch64 (polyMul8 ofVHalves)
open VG.VectorCrypto VG.Proof.Gcm.Poly VG.Proof.Gcm.Clmul
open VG.Impl.Gcm.Clmul (poly)

/-! ## The product of two bytes -/

theorem gp_shl8 (b : BitVec 8) {j : Nat} (hj : j < 8) :
    gp ((b.setWidth 16) <<< j) = X ^ (8 - j) * gp b := by
  ext d
  rw [coeff_gp, coeff_X_pow_mul', coeff_gp, BitVec.getMsbD_shiftLeft, BitVec.getMsbD_setWidth]
  by_cases h : 8 - j ≤ d
  · simp only [h, ite_true, decide_eq_true (show 16 - 8 ≤ d + j by omega_using [h]), Bool.true_and]
    exact congrArg _ (congrArg _ (by omega_using [hj]))
  · simp only [h, ite_false, decide_eq_false (show ¬ 16 - 8 ≤ d + j by omega_using [h]), Bool.false_and]; rfl

/-- The first `k` steps of `polyMul8`. -/
def clSteps8 (a b : BitVec 8) (k : Nat) : BitVec 16 :=
  (List.range k).foldl (fun acc i => if a.getLsbD i then acc ^^^ (b.setWidth 16 <<< i) else acc) 0

theorem gp_clSteps8 (a b : BitVec 8) {k : Nat} (hk : k ≤ 8) :
    gp (clSteps8 a b k) =
      X * (∑ i ∈ Finset.range k, if a.getLsbD i then X ^ (7 - i) else 0) * gp b := by
  induction k with
  | zero => simp only [clSteps8, BitVec.ofNat_eq_ofNat, List.range_zero, List.foldl_nil, gp_zero', Finset.range_zero, Finset.sum_empty, mul_zero, zero_mul]
  | succ k ih =>
    have e : clSteps8 a b (k + 1) =
        if a.getLsbD k then clSteps8 a b k ^^^ (b.setWidth 16 <<< k) else clSteps8 a b k := by
      simp only [clSteps8, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [e, Finset.sum_range_succ]
    split_ifs
    · rw [gp_xor, ih (by omega_using [hk]), gp_shl8 b (by omega_using [hk]),
        show 8 - k = 7 - k + 1 by omega_using [hk], pow_succ]
      ring
    · rw [ih (by omega_using [hk])]; ring

theorem gp_lsb8 (a : BitVec 8) :
    (∑ i ∈ Finset.range 8, if a.getLsbD i then (X : P) ^ (7 - i) else 0) = gp a := by
  rw [gp, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [BitVec.getMsbD_eq_getLsbD, decide_eq_true (by omega_using [hi]), Bool.true_and,
    show 8 - 1 - i = 7 - i by omega_using [], show 7 - (8 - 1 - i) = i by omega_using [hi]]

/-- `pmull` of two bytes multiplies polynomials (with the factor `X` of the
reflected representation). -/
theorem gp_polyMul8 (a b : BitVec 8) : gp (polyMul8 a b) = X * gp a * gp b := by
  rw [show polyMul8 a b = clSteps8 a b 8 from rfl, gp_clSteps8 a b (Nat.le_refl _), gp_lsb8]

/-! ## Bytes -/

theorem bytes64 (q : BitVec 64) :
    q = by8 q 7 ++ by8 q 6 ++ by8 q 5 ++ by8 q 4 ++ by8 q 3 ++ by8 q 2 ++ by8 q 1 ++ by8 q 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [by8, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  have h : i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨ (24 ≤ i ∧ i < 32) ∨ (32 ≤ i ∧ i < 40) ∨
      (40 ≤ i ∧ i < 48) ∨ (48 ≤ i ∧ i < 56) ∨ 56 ≤ i := by omega_using []
  rcases h with h | h | h | h | h | h | h | h <;>
    simp (disch := omega_using [h, hi]) only [↓ite_eq_left, ↓ite_eq_right, Bool.true_and, decide_eq_true] <;> exact congrArg _ (by omega_using [h, hi])

/-- A doubleword's polynomial, from its bytes'. -/
theorem gp_bytes (q : BitVec 64) :
    gp q = X ^ 56 * gp (by8 q 0) + X ^ 48 * gp (by8 q 1) + X ^ 40 * gp (by8 q 2) +
      X ^ 32 * gp (by8 q 3) + X ^ 24 * gp (by8 q 4) + X ^ 16 * gp (by8 q 5) + X ^ 8 * gp (by8 q 6) +
      gp (by8 q 7) := by
  conv_lhs => rw [bytes64 q]
  simp only [gp_append]
  ring

theorem by8_ushr (q : BitVec 64) (d i : Nat) :
    by8 (q >>> (8 * d)) i = if i + d < 8 then by8 q (i + d) else 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  split_ifs with h
  · simp only [by8, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight, hk, decide_true, Bool.true_and]
    exact congrArg _ (by omega_using [])
  · simp only [by8, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight, hk, decide_true, Bool.true_and,
      BitVec.ofNat_eq_ofNat, BitVec.getLsbD_zero]
    exact BitVec.getLsbD_of_ge q _ (by omega_using [h])

theorem by8_shl (q : BitVec 64) (d i : Nat) :
    by8 (q <<< (8 * d)) i = if d ≤ i ∧ i < 8 then by8 q (i - d) else 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  split_ifs with h
  · simp only [by8, BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft, hk, decide_true, Bool.true_and,
      decide_eq_true (show 8 * i + k < 64 by omega_using [h, hk]),
      decide_eq_false (show ¬ 8 * i + k < 8 * d by omega_using [h]), Bool.not_false]
    exact congrArg _ (by omega_using [h])
  · simp only [by8, BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft, hk, decide_true, Bool.true_and]
    by_cases h8 : i < 8
    · simp only [decide_eq_true (show 8 * i + k < 8 * d by omega_using [h, h8, hk]), Bool.not_true, Bool.false_and,
        Bool.and_false, BitVec.ofNat_eq_ofNat, BitVec.getLsbD_zero]
    · simp only [decide_eq_false (show ¬ 8 * i + k < 64 by omega_using [h8]), Bool.false_and, BitVec.ofNat_eq_ofNat, BitVec.getLsbD_zero]

/-! ## `pmull` of eight pairs of bytes -/

theorem gp_pmB (a b : BitVec 64) :
    gp (pmB a b) = X * (X ^ 112 * (gp (by8 a 0) * gp (by8 b 0)) + X ^ 96 * (gp (by8 a 1) * gp (by8 b 1)) +
      X ^ 80 * (gp (by8 a 2) * gp (by8 b 2)) + X ^ 64 * (gp (by8 a 3) * gp (by8 b 3)) +
      X ^ 48 * (gp (by8 a 4) * gp (by8 b 4)) + X ^ 32 * (gp (by8 a 5) * gp (by8 b 5)) +
      X ^ 16 * (gp (by8 a 6) * gp (by8 b 6)) + gp (by8 a 7) * gp (by8 b 7)) := by
  simp only [pmB, ofVHalves, gp_append, gp_polyMul8]
  ring

theorem polyMul8_zero_left (b : BitVec 8) : polyMul8 0 b = 0 :=
  gp_ext (by rw [gp_polyMul8, gp_zero, mul_zero, zero_mul, gp_zero])

theorem polyMul8_zero_right (a : BitVec 8) : polyMul8 a 0 = 0 :=
  gp_ext (by rw [gp_polyMul8, gp_zero, mul_zero, gp_zero])

/-- The top byte of `pmB` is of the product of the top bytes. -/
theorem msb_pmB (a b : BitVec 64) {i : Nat} (hi : i < 8) :
    (pmB a b).getMsbD i = (polyMul8 (by8 a 7) (by8 b 7)).getMsbD i := by
  simp only [pmB, ofVHalves, BitVec.getMsbD_append]
  simp (disch := omega_using [hi]) only [↓ite_eq_right]

theorem msb_pmB_left (a b : BitVec 64) (h : by8 a 7 = 0) {i : Nat} (hi : i < 8) :
    (pmB a b).getMsbD i = false := by
  rw [msb_pmB a b hi, h, polyMul8_zero_left]; simp only [BitVec.ofNat_eq_ofNat, BitVec.getMsbD_zero]

theorem msb_pmB_right (a b : BitVec 64) (h : by8 b 7 = 0) {i : Nat} (hi : i < 8) :
    (pmB a b).getMsbD i = false := by
  rw [msb_pmB a b hi, h, polyMul8_zero_right]; simp only [BitVec.ofNat_eq_ofNat, BitVec.getMsbD_zero]

/-- A shift up by a byte divides by `X⁸`, if that byte is clear. -/
theorem gp_shl_byte (v : BitVec 128) (h : ∀ i < 8, v.getMsbD i = false) :
    X ^ 8 * gp (v <<< 8) = gp v := by
  ext d
  rw [coeff_X_pow_mul', coeff_gp, coeff_gp, BitVec.getMsbD_shiftLeft]
  by_cases h8 : 8 ≤ d
  · simp only [h8, ite_true, Nat.sub_add_cancel h8]
  · simp only [h8, ite_false, h d (by omega_using [h8])]; rfl

theorem by8_ushr8 (q : BitVec 64) (i : Nat) : by8 (q >>> 8) i = if i + 1 < 8 then by8 q (i + 1) else 0 :=
  by8_ushr q 1 i
theorem by8_ushr16 (q : BitVec 64) (i : Nat) : by8 (q >>> 16) i = if i + 2 < 8 then by8 q (i + 2) else 0 :=
  by8_ushr q 2 i
theorem by8_ushr24 (q : BitVec 64) (i : Nat) : by8 (q >>> 24) i = if i + 3 < 8 then by8 q (i + 3) else 0 :=
  by8_ushr q 3 i
theorem by8_ushr32 (q : BitVec 64) (i : Nat) : by8 (q >>> 32) i = if i + 4 < 8 then by8 q (i + 4) else 0 :=
  by8_ushr q 4 i
theorem by8_shl8 (q : BitVec 64) (i : Nat) : by8 (q <<< 8) i = if 1 ≤ i ∧ i < 8 then by8 q (i - 1) else 0 :=
  by8_shl q 1 i
theorem by8_shl16 (q : BitVec 64) (i : Nat) : by8 (q <<< 16) i = if 2 ≤ i ∧ i < 8 then by8 q (i - 2) else 0 :=
  by8_shl q 2 i
theorem by8_shl24 (q : BitVec 64) (i : Nat) : by8 (q <<< 24) i = if 3 ≤ i ∧ i < 8 then by8 q (i - 3) else 0 :=
  by8_shl q 3 i

theorem msb_cl1 (a b : BitVec 64) {i : Nat} (hi : i < 8) : (cl1 a b).getMsbD i = false := by
  simp only [cl1, BitVec.getMsbD_xor]
  rw [msb_pmB_right _ _ (by rw [by8_ushr8]; rfl) hi, msb_pmB_left _ _ (by rw [by8_ushr8]; rfl) hi,
    msb_pmB_left _ _ (by rw [by8_ushr16]; rfl) hi, msb_pmB_left _ _ (by rw [by8_ushr24]; rfl) hi,
    msb_pmB_left _ _ (by rw [by8_ushr32]; rfl) hi, msb_pmB_right _ _ (by rw [by8_ushr16]; rfl) hi,
    msb_pmB_right _ _ (by rw [by8_ushr24]; rfl) hi, msb_pmB_right _ _ (by rw [by8_ushr32]; rfl) hi]
  rfl

/-- Fifteen `pmull`s of bytes make the `pmull` of two doublewords. -/
theorem cl_polyMul (a b : BitVec 64) : cl0 a b ^^^ (cl1 a b <<< 8) = polyMul a b := by
  apply gp_ext
  apply mul_left_cancel₀ (pow_ne_zero 8 (X_ne_zero (R := ZMod 2)))
  rw [gp_xor, mul_add, gp_shl_byte _ fun i hi => msb_cl1 a b hi, gp_polyMul, gp_bytes a, gp_bytes b]
  simp only [cl0, cl1, gp_xor, gp_pmB, by8_ushr8, by8_ushr16, by8_ushr24, by8_ushr32, by8_shl8, by8_shl16,
    by8_shl24, Nat.reduceAdd, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceSub, and_true, and_self, ↓reduceIte, gp_zero, zero_mul, mul_zero, add_zero, zero_add]
  ring

/-! ## The reduction

The 256 bits of a product, `hi : mid : lo` with `hi` holding the low powers,
are four doublewords `I₃ : I₂ : I₁ : I₀`. `x¹²⁸ = 1 + x + x² + x⁷` folds
`I₀` into `I₂` and `I₁`, then `I₁` into `I₃` and `I₂`: the part of
`(1 + x + x² + x⁷) · I` that stays in its doubleword is `I ⊕ I ≫ 1 ⊕ I ≫ 2
⊕ I ≫ 7`, and what leaves it for the next is `I ≪ 63 ⊕ I ≪ 62 ⊕ I ≪ 57`. -/

/-- A shift of a doubleword down by `k` bits multiplies by `xᵏ`, but for
the bits that leave it. -/
theorem gp_split (v : BitVec 64) {k : Nat} (hk : k < 64) :
    X ^ k * gp v = gp (v >>> k) + X ^ 64 * gp (v <<< (64 - k)) := by
  ext d
  rw [coeff_add, coeff_X_pow_mul', coeff_X_pow_mul', coeff_gp, coeff_gp, coeff_gp,
    BitVec.getMsbD_ushiftRight, BitVec.getMsbD_shiftLeft]
  rcases (by omega_using [hk] : d < k ∨ (k ≤ d ∧ d < 64) ∨ 64 ≤ d) with h | h | h
  · simp [show ¬ k ≤ d by omega_using [h], h, show ¬ 64 ≤ d by omega_using [h, hk], bit]
  · simp [h.1, h.2, show ¬ d < k by omega_using [h], show ¬ 64 ≤ d by omega_using [h]]
  · simp [show k ≤ d by omega_using [h, hk], show ¬ d < 64 by omega_using [h], h, bit,
      show d - 64 + (64 - k) = d - k by omega_using [h, hk]]

theorem ψ_split (v : BitVec 64) {k : Nat} (hk : k < 64) :
    x ^ k * ψ v = ψ (v >>> k) + x ^ 64 * ψ (v <<< (64 - k)) := by
  have h := congrArg (AdjoinRoot.mk g) (gp_split v hk)
  simp only [map_add, map_mul, map_pow, AdjoinRoot.mk_X] at h
  exact h

/-- What leaves a doubleword leaves the next one too. -/
theorem carry_shl (q : BitVec 64) {s : Nat} (hs : 7 ≤ s) :
    (q <<< 63 ^^^ q <<< 62 ^^^ q <<< 57) <<< s = 0#64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [show i - s < 63 by omega_using [hi, hs], show i - s < 62 by omega_using [hi, hs],
    show i - s < 57 by omega_using [hi, hs]]

theorem ψ_zero : ψ 0#64 = 0 := by simp only [ψ, gp_zero', map_zero]

theorem vdword_zero (e : Nat) : vdword 0#128 e = 0#64 := by
  simp only [VG.Proof.Gcm.Clmul.vdword, BitVec.extractLsb'_zero]

theorem ρ_fold (lo hi : BitVec 128) : ρ (fold lo hi) = φ hi + x ^ 128 * φ lo := by
  simp only [fold]
  rw [ρ_ext8_self, φ_v, φ_v hi, φ_v lo]
  simp only [vdword_xor, vdword_ext8_0, vdword_ext8_1, vdword_zero, sl, sr, VG.Proof.Gcm.Clmul.ofVDwords,
    vdword_append_0,
    vdword_append_1, BitVec.xor_zero]
  generalize vdword lo 0 = a0
  generalize vdword lo 1 = a1
  generalize vdword hi 0 = h0
  generalize vdword hi 1 = h1
  have hw : ∀ s, 7 ≤ s → (a1 ^^^ (a0 <<< 63 ^^^ a0 <<< 62 ^^^ a0 <<< 57)) <<< s = a1 <<< s := fun s hs => by
    rw [BitVec.shiftLeft_xor_distrib, carry_shl a0 hs, BitVec.xor_zero]
  have w1 := ψ_split (a1 ^^^ (a0 <<< 63 ^^^ a0 <<< 62 ^^^ a0 <<< 57)) (k := 1) (by decide)
  have w2 := ψ_split (a1 ^^^ (a0 <<< 63 ^^^ a0 <<< 62 ^^^ a0 <<< 57)) (k := 2) (by decide)
  have w7 := ψ_split (a1 ^^^ (a0 <<< 63 ^^^ a0 <<< 62 ^^^ a0 <<< 57)) (k := 7) (by decide)
  rw [hw _ (by decide)] at w1 w2 w7
  have b1 := ψ_split a0 (k := 1) (by decide)
  have b2 := ψ_split a0 (k := 2) (by decide)
  have b7 := ψ_split a0 (k := 7) (by decide)
  have hW : ψ (a1 ^^^ (a0 <<< 63 ^^^ a0 <<< 62 ^^^ a0 <<< 57)) =
      ψ a1 + ψ (a0 <<< 63) + ψ (a0 <<< 62) + ψ (a0 <<< 57) := by
    simp only [ψ_xor]; ring
  simp only [ψ_xor]
  simp only [Nat.reduceSub] at w1 w2 w7 b1 b2 b7
  linear_combination (-1 : Q) * w1 + (-1 : Q) * w2 + (-1 : Q) * w7 + (-x ^ 64) * b1 + (-x ^ 64) * b2 +
    (-x ^ 64) * b7 + (x + x ^ 2 + x ^ 7) * hW +
    (-(ψ a1 + ψ (a0 <<< 63) + ψ (a0 <<< 62) + ψ (a0 <<< 57) + x ^ 64 * ψ a0)) * x128

theorem ρ_reduceN (p : Prod) : ρ (reduceN p) = p.val := by
  rw [reduceN, ρ_fold, φ_xor, φ_xor, φ_ext8, φ_ext8, Prod.val, φ_v p.mid, vdword_zero, vdword_zero, ψ_zero]
  ring

theorem mulN_eq (a t : BitVec 128) : mulN a (ext8 t t) = mulV a t := by
  apply Pmull.ρ_inj
  rw [ρ_mulV, mulN, ρ_reduceN, Prod.val, φ_xor, φ_xor, φ_polyMul, φ_polyMul, φ_polyMul, ψ_xor, ψ_xor,
    vdword_ext8_0, vdword_ext8_1, ρ, φ_v t]
  linear_combination (x ^ 65 * (ψ (vdword a 0) * ψ (vdword t 1) + ψ (vdword a 1) * ψ (vdword t 0))) * two_Q

/-! ## The key -/

/-- `sshr #63` is the mask of the top bit. -/
theorem sshr63 (q : BitVec 64) : q.sshiftRight 63 = if q.getMsbD 0 then BitVec.allOnes 64 else 0#64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hm : (if 63 + i < 64 then q.getLsbD (63 + i) else q.msb) = q.msb := by
    split_ifs with h
    · obtain rfl : i = 0 := by omega_using [h]
      rw [BitVec.msb_eq_getLsbD_last]
    · rfl
  rw [BitVec.getLsbD_sshiftRight, hm, decide_eq_false (by omega_using [hi]), Bool.not_false, Bool.true_and]
  change q.getMsbD 0 = _
  cases q.getMsbD 0
  · simp
  · simp only [ite_true, BitVec.getLsbD_allOnes, hi, decide_true]

theorem and_ofVDwords (a b c d : BitVec 64) :
    ofVDwords a b &&& ofVDwords c d = ofVDwords (a &&& c) (b &&& d) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [VG.Proof.Gcm.Clmul.ofVDwords, BitVec.getLsbD_and, BitVec.getLsbD_append]
  by_cases h : i < 64 <;> simp only [h, ite_true, ite_false]

/-- The reduction constant under the mask of the top bit of the low
doubleword is its `pmull` by that bit. -/
theorem mask_poly (a : BitVec 128) :
    ofVDwords ((vdword a 0).sshiftRight 63) ((vdword a 1).sshiftRight 63) &&& ofVDwords poly 0#64 =
      polyMul (vdword a 0 >>> 63) poly := by
  rw [and_ofVDwords, ushr63, sshr63, BitVec.and_zero]
  cases (vdword a 0).getMsbD 0
  · simp only [Bool.false_eq_true, ite_false, BitVec.zero_and]
    exact (polyMul_zero_left poly).symm
  · simp only [ite_true, BitVec.allOnes_and]
    decide +kernel

theorem twistV_ρ' (a : BitVec 128) : x * ρ (twistV a) = ρ a := by
  rw [twistV, mask_poly]; exact twistV_ρ a

/-- `twist` computes the key of `vg_ghash_aes`. -/
theorem twistV_key (H : Spec.Gcm.Block) :
    ext8 (twistV (ext8 H H)) (twistV (ext8 H H)) = Pmull.keyV H := by
  apply φ_inj
  apply Pmull.x_cancel
  rw [φ_ext8_self, twistV_ρ', ρ_ext8_self, Pmull.keyV, φ_ext8_self, ρ_mulV, ρ_ext8_self]
  linear_combination (-(φ H)) * x2_φ_xInv2

theorem arith : Arith :=
  ⟨cl_polyMul, fun a b _ hi => msb_cl1 a b hi, mulN_eq, twistV_key, Pmull.mulV_keyV⟩

end VG.Proof.Gcm.AArch64.Neon

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64

/-- `vg_ghash_prepared8_aes`, with PMULL. -/
def GhashPreparedImpl.aes : GhashPreparedImpl where
  fn := ⟨"vg_ghash_prepared8_aes", Impl.Gcm.AArch64.Pmull.ghashP⟩
  noFrames := by decide +kernel
  ok := Proof.Gcm.AArch64.Pmull.ghashP_correct
  ct := Proof.Gcm.AArch64.Pmull.ghashP_ct
  keepsV := by decide +kernel

/-- `vg_ghash_with_powers_aes`, with PMULL. -/
def GhashWithImpl.aes : GhashWithImpl where
  fn := ⟨"vg_ghash_with_powers_aes", Impl.Gcm.AArch64.Pmull.ghashW⟩
  noFrames := by decide +kernel
  ok := Proof.Gcm.AArch64.Pmull.ghashW_correct
  ct := Proof.Gcm.AArch64.Pmull.ghashW_ct
  keepsV := by decide +kernel

namespace GhashImpl

/-- `vg_ghash`, in the baseline ISA. -/
def scalar : GhashImpl where
  fn := ⟨"vg_ghash", Impl.Gcm.AArch64.ghash⟩
  noFrames := by lit_decide
  ok := Proof.Gcm.AArch64.ghash_correct
  ct := Proof.Gcm.AArch64.ghash_ct
  keepsV := by lit_decide
  suffix := ""
  features := []

/-- `vg_ghash_aes`, with PMULL (which Rust's `aes` feature stands for, with
the AES instructions). -/
def aes : GhashImpl where
  fn := ⟨"vg_ghash_aes", Impl.Gcm.AArch64.Pmull.ghash⟩
  noFrames := by decide +kernel
  ok := Proof.Gcm.AArch64.Pmull.ghash_correct
  ct := Proof.Gcm.AArch64.Pmull.ghash_ct
  keepsV := by decide +kernel
  suffix := "_aes"
  features := ["aes"]
  pmull := true
  prepared := some .aes
  withPowers := some .aes

/-- `vg_ghash_neon`, with the `pmull` of bytes, which AdvSIMD has without
PMULL. -/
def neon : GhashImpl where
  fn := ⟨"vg_ghash_neon", Impl.Gcm.AArch64.Neon.ghash⟩
  noFrames := by decide +kernel
  ok := Proof.Gcm.AArch64.Neon.ghash_correct Proof.Gcm.AArch64.Neon.arith
  ct := Proof.Gcm.AArch64.Neon.ghash_ct
  keepsV := by decide +kernel
  suffix := "_neon"
  features := []

end GhashImpl

/-- The implementation of `vg_ghash` named `n`. -/
def GhashName.impl : GhashName → GhashImpl
  | .scalar => .scalar
  | .aes => .aes
  | .neon => .neon

/-- The implementations a variant calls. -/
def GcmVariant.impl (v : GcmVariant) : GcmImpl := ⟨v.ctr, v.key, v.gh.impl, v.stitch⟩

end VG.Proof.AesGcm.AArch64

namespace VG.Proof.Gcm.AArch64.Stitch

open VG VG.AArch64 VG.Proof.Gcm.Poly VG.Proof.Gcm.AArch64.Pmull
open VG.Impl.Gcm.AArch64.Stitch (pa pb pk pl)

/-- `kadd` adds `x · a · s` (`s` as loaded) to the product. -/
theorem val_fix_kadd (p : Prod) (a s : BitVec 128) :
    (fix (kadd p a s (kkey s))).val = (fix p).val + x * ρ a * ρ s := by
  simp only [fix, kadd, kkey, Prod.val, φ_xor, φ_polyMul, ψ_xor, ρ]
  linear_combination (x ^ 65 * (ψ (vdword a 0) * ψ (vdword s 0) + ψ (vdword a 1) * ψ (vdword s 1))) *
    two_Q

theorem vdword_ofVDwords_0 (a b : BitVec 64) : vdword (ofVDwords a b) 0 = a := vdword_append_0 _ _
theorem vdword_ofVDwords_1 (a b : BitVec 64) : vdword (ofVDwords a b) 1 = b := vdword_append_1 _ _

theorem val_fix_zero : (fix ⟨0#128, 0#128, 0#128⟩).val = 0 := by
  simp only [fix, Prod.val, BitVec.xor_zero, φ_zero', mul_zero, add_zero]

/-- A pair's products, from the keys of the table. -/
theorem val_kpair (pv : Prod) (H : Spec.Gcm.Block) (a₁ a₂ : BitVec 128) (k l : Nat) :
    (fix (kpair pv a₁ (ext8 (pp H k) (pp H k)) a₂ (ext8 (pp H l) (pp H l)) (kpack H k l))).val =
      (fix pv).val + ρ a₁ * φ H ^ k + ρ a₂ * φ H ^ l := by
  rw [kpair, kpack, vdword_ofVDwords_0, vdword_ofVDwords_1, val_fix_kadd, val_fix_kadd, ρ_ext8_self,
    ρ_ext8_self, ← x_φ_pp H k, ← x_φ_pp H l]
  ring

theorem gh8Ok : Gh8Ok := by
  intro H y b
  apply ρ_inj
  simp only [gh8V, pk, pl, pa, pb, show (0 : Nat) = 3 ↔ False by decide, show (1 : Nat) = 3 ↔ False by decide,
    show (2 : Nat) = 3 ↔ False by decide, ite_false, ite_true, BitVec.ofNat_eq_ofNat, BitVec.xor_zero]
  rw [ρ_reduce, val_kpair, val_kpair, val_kpair, val_kpair, val_fix_zero, ρ_ext8_self, ρ_xor]
  simp only [ρ_ext8_self, Spec.Gcm.ghashFrom, List.range_succ, List.range_zero, List.map_append, List.map_cons,
    List.map_nil, List.nil_append, List.foldl_append, List.foldl_cons, List.foldl_nil, φ_mul, φ_xor]
  ring

end VG.Proof.Gcm.AArch64.Stitch
