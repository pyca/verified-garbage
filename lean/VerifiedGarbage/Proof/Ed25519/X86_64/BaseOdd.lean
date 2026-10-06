import VerifiedGarbage.Impl.Ed25519.X86_64.BaseOdd
import VerifiedGarbage.Proof.Ed25519.WindowConstants
import VerifiedGarbage.Proof.Ed25519.Recode

/-!
# The static odd multiples of `-B`

`checkOdd` walks `baseOddAffine` a pair of entries at a time, comparing them projectively with
`[2m + 1]B` and its negation and adding `[2]B` with the specification's formula as it goes, so
the kernel evaluates 64 additions; each static entry is the caching of the negation of its
affine point by definition, so entry `e` represents `-[d]B` for the digit `d = dec (e + 1)`
whose byte is `e + 1` (`baseOddCached_ok`).
-/

namespace VG.Proof.Ed25519.X86_64

open VG.Spec.Ed25519 VG.Impl.Ed25519.X86_64 VG.Proof.Ed25519 Edwards
open Spec.X25519 (Fe)

/-- `(x, y)` is the affine point of the projective `p`. -/
private def same (q : Fe × Fe) (p : Point) : Bool := q.1 * p.Z == p.X && q.2 * p.Z == p.Y && p.Z != 0

private theorem same_rep {q : Fe × Fe} {p : Point} {a : EPoint dZ} (h : Rep p a) (hs : same q p = true) :
    Rep (affPt q) a := by
  simp only [same, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hs
  obtain ⟨⟨hx, hy⟩, _⟩ := hs
  refine h.of_proj (show toZ 1 ≠ 0 by decide) ?_ ?_
    (by show toZ (q.1 * q.2) * toZ 1 = toZ q.1 * toZ q.2; rw [toZ_mul, toZ_one, mul_one])
  · show toZ q.1 * toZ p.Z = toZ p.X * toZ 1
    rw [toZ_one, mul_one, ← toZ_mul, hx]
  · show toZ q.2 * toZ p.Z = toZ p.Y * toZ 1
    rw [toZ_one, mul_one, ← toZ_mul, hy]

/-- Entries `2m` and `2m + 1` are `p` and `-p`, `p` moving on by `b2`. -/
private def checkOdd (b2 p : Point) : List (Fe × Fe) → Bool
  | q :: q' :: qs => same q p && same q' (negPoint p) && checkOdd b2 (pointAdd (affPt q) b2) qs
  | _ => true

private theorem checkOdd_ok (b2 : Point) (c : EPoint dZ) (hb : Rep b2 c) (p : Point) (a : EPoint dZ)
    (h : Rep p a) (qs : List (Fe × Fe)) (hc : checkOdd b2 p qs = true) (hl : qs.length % 2 = 0)
    (m : Nat) (hm : 2 * m + 1 < qs.length) :
    Rep (affPt (qs.getD (2 * m) (0, 1))) (a + m • c) ∧
      Rep (affPt (qs.getD (2 * m + 1) (0, 1))) (-(a + m • c)) := by
  induction m generalizing p a qs with
  | zero =>
    match qs, hc, hm with
    | q :: q' :: qs, hc, _ =>
      simp only [checkOdd, Bool.and_eq_true] at hc
      simp only [zero_smul, add_zero, List.getD_cons_zero, Nat.mul_zero, Nat.zero_add, List.getD_cons_succ]
      exact ⟨same_rep h hc.1.1, same_rep h.neg hc.1.2⟩
  | succ m ih =>
    match qs, hc, hm, hl with
    | q :: q' :: qs, hc, hm, hl =>
      simp only [checkOdd, Bool.and_eq_true] at hc
      simp only [List.length_cons] at hm hl
      have := ih (pointAdd (affPt q) b2) (a + c) (pointAdd_rep (same_rep h hc.1.1) hb) qs hc.2
        (by omega) (by omega)
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega, List.getD_cons_succ, List.getD_cons_succ,
        show 2 * m + 1 + 1 + 1 = 2 * m + 1 + 1 + 1 from rfl, List.getD_cons_succ, List.getD_cons_succ,
        succ_nsmul, show a + (m • c + c) = a + c + m • c by abel]
      exact this

private theorem odd_check : checkOdd (pointAdd basePoint basePoint) basePoint baseOddAffine = true := by
  decide +kernel

theorem baseOddAffine_length : baseOddAffine.length = 128 := by decide +kernel

/-- Entry `e < 128` of the static is the caching of a representative of `[dec (e + 1)](-B)`. -/
theorem baseOddCached_ok (e : Nat) (he : e < 128) :
    ∃ q, baseOddCached (baseOddAffine.getD e (0, 1)) = cache q ∧
      Rep q ((Recode.dec (e + 1)) • (-baseAff)) := by
  refine ⟨negPoint (affPt (baseOddAffine.getD e (0, 1))), rfl, ?_⟩
  have h := checkOdd_ok _ _ (pointAdd_rep basePoint_rep basePoint_rep) _ _ basePoint_rep _ odd_check
    (by rw [baseOddAffine_length]) (e / 2) (by rw [baseOddAffine_length]; omega)
  rw [smul_neg]
  apply Rep.neg
  rcases Nat.even_or_odd' e with ⟨m, rfl | rfl⟩
  · rw [show 2 * m / 2 = m by omega] at h
    have hd : Recode.dec (2 * m + 1) = ((2 * m + 1 : Nat) : Int) := Recode.dec_odd (by omega)
    rw [hd, natCast_zsmul]
    convert h.1 using 1
    rw [add_smul, mul_smul, one_smul, two_smul, ← two_nsmul, two_nsmul, smul_add]; abel
  · rw [show (2 * m + 1) / 2 = m by omega] at h
    have hd : Recode.dec (2 * m + 1 + 1) = -((2 * m + 1 : Nat) : Int) := by
      rw [Recode.dec_even (by omega) (by omega)]; push_cast; ring
    rw [hd, neg_smul, natCast_zsmul]
    convert h.2 using 2
    rw [add_smul, mul_smul, one_smul, two_smul, ← two_nsmul, two_nsmul, smul_add]; abel

end VG.Proof.Ed25519.X86_64
