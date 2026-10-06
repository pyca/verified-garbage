import VerifiedGarbage.Impl.Ed25519.X86_64.BaseBytes
import VerifiedGarbage.Proof.Ed25519.WindowConstants

/-!
# The static multiples of `-B` represent `-[i + 1]B`

`checkBytes` walks `baseBytesAffine` once, adding the base point with the specification's
formula as it goes and comparing projectively, so the kernel evaluates 254 additions; each
static entry is the caching of the negation of its affine point by definition.
-/

namespace VG.Proof.Ed25519.X86_64

open VG.Spec.Ed25519 VG.Impl.Ed25519.X86_64 VG.Proof.Ed25519 Edwards
open Spec.X25519 (Fe)

private def checkBytes (p : Point) : List (Fe × Fe) → Bool
  | [] => true
  | q :: qs => (q.1 * p.Z == p.X && q.2 * p.Z == p.Y && p.Z != 0) &&
      checkBytes (pointAdd (affPt q) basePoint) qs

private theorem checkBytes_ok (p : Point) (a : EPoint dZ) (h : Rep p a) (qs : List (Fe × Fe))
    (hc : checkBytes p qs = true) (i : Nat) (hi : i < qs.length) :
    Rep (affPt (qs.getD i (0, 1))) (i • baseAff + a) := by
  induction qs generalizing p a i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons q qs ih =>
    simp only [checkBytes, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hc
    obtain ⟨⟨⟨hx, hy⟩, _⟩, hrest⟩ := hc
    have hq : Rep (affPt q) a := by
      refine h.of_proj (show toZ 1 ≠ 0 by decide) ?_ ?_
        (by show toZ (q.1 * q.2) * toZ 1 = toZ q.1 * toZ q.2; rw [toZ_mul, toZ_one, mul_one])
      · show toZ q.1 * toZ p.Z = toZ p.X * toZ 1
        rw [toZ_one, mul_one, ← toZ_mul, hx]
      · show toZ q.2 * toZ p.Z = toZ p.Y * toZ 1
        rw [toZ_one, mul_one, ← toZ_mul, hy]
    cases i with
    | zero => simpa using hq
    | succ i =>
      have := ih _ _ (pointAdd_rep hq basePoint_rep) hrest i (by simp only [List.length_cons] at hi; omega)
      rw [List.getD_cons_succ, succ_nsmul, add_assoc, add_comm baseAff a]
      exact this

private theorem bytes_check : checkBytes basePoint baseBytesAffine = true := by decide +kernel

theorem baseBytesAffine_length : baseBytesAffine.length = 255 := by decide +kernel

/-- Entry `i < 255` of the static is the caching of a representative of `-[i + 1]B`. -/
theorem baseByteCached_ok (i : Nat) (hi : i < 255) :
    ∃ q, baseByteCached (baseBytesAffine.getD i (0, 1)) = cache q ∧ Rep q ((i + 1) • (-baseAff)) := by
  refine ⟨negPoint (affPt (baseBytesAffine.getD i (0, 1))), rfl, ?_⟩
  have h := checkBytes_ok basePoint baseAff basePoint_rep baseBytesAffine bytes_check i
    (baseBytesAffine_length ▸ hi)
  rw [← succ_nsmul] at h
  rw [smul_neg]; exact h.neg

end VG.Proof.Ed25519.X86_64
