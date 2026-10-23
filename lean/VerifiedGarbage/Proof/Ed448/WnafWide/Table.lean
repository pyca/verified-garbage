module

public import VerifiedGarbage.Impl.Ed448.PublicTable
public import VerifiedGarbage.Proof.X448.BaseTable

/-! Every public verification entry is the stated odd multiple of B. -/

@[expose] public section

namespace VG.Proof.Ed448.WnafWide

open VG.Spec.Ed448 VG.Proof.Ed448 VG.Proof.EdwardsLaw
open VG.Spec.X448 (Fe)
open VG.Proof.X448 (basePt basePt_rep)

private def checkRow (step p : Point) : List (Fe × Fe) → Bool
  | [] => true
  | q :: qs => (q.1 * p.Z == p.X && q.2 * p.Z == p.Y) &&
      checkRow step (pointAdd (basePt q) step) qs

private theorem checkRow_ok (b p : Point) (c a : EPoint dZ) (hb : Rep b c) (h : Rep p a)
    (qs : List (Fe × Fe)) (hc : checkRow b p qs = true) (i : Nat) (hi : i < qs.length) :
    Rep (basePt (qs.getD i (0, 1))) (i • c + a) := by
  induction qs generalizing p a i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons q qs ih =>
    simp only [checkRow, Bool.and_eq_true, beq_iff_eq] at hc
    have hq : Rep (basePt q) a := basePt_rep h hc.1.1 hc.1.2
    cases i with
    | zero => rw [List.getD_cons_zero, zero_nsmul, zero_add]; exact hq
    | succ i =>
      have hh := ih _ _ (pointAdd_rep hq hb) hc.2 i (by simp only [List.length_cons] at hi; omega)
      rw [List.getD_cons_succ, succ_nsmul, add_assoc, add_comm c a]
      exact hh

private theorem table_check :
    checkRow (pointAdd basePoint basePoint) basePoint Impl.Ed448.PublicTable.rows = true := by
  decide +kernel

theorem publicTable_length : Impl.Ed448.PublicTable.rows.length = 64 := by decide +kernel

theorem publicTable_rep (i : Nat) (hi : i < 64) :
    Rep (basePt (Impl.Ed448.PublicTable.entry i)) ((2 * i + 1) • baseAff) := by
  have h2 : Rep (pointAdd basePoint basePoint) ((2 : Nat) • baseAff) := by
    rw [two_nsmul]
    exact pointAdd_rep basePoint_rep basePoint_rep
  have h := checkRow_ok _ _ _ _ h2 basePoint_rep _ table_check i (by rw [publicTable_length]; exact hi)
  simpa only [smul_smul, add_nsmul, one_nsmul, Nat.mul_comm, Impl.Ed448.PublicTable.entry] using h

end VG.Proof.Ed448.WnafWide
