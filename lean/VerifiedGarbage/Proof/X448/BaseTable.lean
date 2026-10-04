import VerifiedGarbage.Impl.X448.BaseTable
import VerifiedGarbage.Proof.Ed448.Group.Projective

/-!
# The fixed-base tables represent `[k 256^j] B`, and `baseG` represents `[G] B`

`checkTables` walks the tables once (as `Proof/Ed25519/CombDigits.lean` does
Ed25519's): within table `j`, each entry is the previous one plus the first,
with the specification's `pointAdd`, compared projectively; the first entry of
table `j + 1` is `[256]` of table `j`'s, with the specification's `pointMul`.
The kernel evaluates it (`tables_check`).
-/

namespace VG.Proof.X448

open VG.Spec.Ed448 VG.Impl.X448 VG.Proof.Ed448 VG.Proof.Ed448.Edwards
open Spec.X448 (Fe)

/-- The projective point `(x, y, 1)`. -/
def basePt (q : Fe × Fe) : Point := ⟨q.1, q.2, 1⟩

theorem basePt_rep {p : Point} {a : EPoint dZ} (h : Rep p a) {q : Fe × Fe}
    (hx : q.1 * p.Z = p.X) (hy : q.2 * p.Z = p.Y) : Rep (basePt q) a := by
  refine h.of_proj (show Ed448.toZ 1 ≠ 0 by rw [toZ_one]; exact one_ne_zero) ?_ ?_
  · show Ed448.toZ q.1 * Ed448.toZ p.Z = Ed448.toZ p.X * Ed448.toZ 1
    rw [toZ_one, mul_one, ← toZ_mul, hx]
  · show Ed448.toZ q.2 * Ed448.toZ p.Z = Ed448.toZ p.Y * Ed448.toZ 1
    rw [toZ_one, mul_one, ← toZ_mul, hy]

/-- The entries `p`, `p + b`, `p + 2b`, …, each compared with `p`'s representative. -/
private def checkRow (b p : Point) : List (Fe × Fe) → Bool
  | [] => true
  | q :: qs => (q.1 * p.Z == p.X && q.2 * p.Z == p.Y && p.Z != 0) &&
      checkRow b (pointAdd (basePt q) b) qs

private theorem checkRow_ok (b p : Point) (c a : EPoint dZ) (hb : Rep b c) (h : Rep p a)
    (qs : List (Fe × Fe)) (hc : checkRow b p qs = true) (i : Nat) (hi : i < qs.length) :
    Rep (basePt (qs.getD i (0, 1))) (i • c + a) := by
  induction qs generalizing p a i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons q qs ih =>
    simp only [checkRow, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hc
    obtain ⟨⟨⟨hx, hy⟩, _⟩, hrest⟩ := hc
    have hq : Rep (basePt q) a := basePt_rep h hx hy
    cases i with
    | zero => rw [List.getD_cons_zero, zero_nsmul, zero_add]; exact hq
    | succ i =>
      have := ih _ _ (pointAdd_rep hq hb) hrest i (by simp only [List.length_cons] at hi; omega)
      rw [List.getD_cons_succ, succ_nsmul, add_assoc, add_comm c a]
      exact this

/-- Each table checked from the representative `b` of its first entry. -/
private def checkTables (b : Point) : List (List (Fe × Fe)) → Bool
  | [] => true
  | row :: rows => checkRow b b row && checkTables (pointMul 256 b) rows

private theorem checkTables_ok (b : Point) (c : EPoint dZ) (hb : Rep b c)
    (rows : List (List (Fe × Fe))) (hc : checkTables b rows = true) (j : Nat) (hj : j < rows.length)
    (k : Nat) (hk : k < (rows.getD j []).length) :
    Rep (basePt ((rows.getD j []).getD k (0, 1))) ((k + 1) • ((256 ^ j) • c)) := by
  induction rows generalizing b c j with
  | nil => exact absurd hj (Nat.not_lt_zero _)
  | cons row rows ih =>
    simp only [checkTables, Bool.and_eq_true] at hc
    cases j with
    | zero =>
      rw [List.getD_cons_zero] at hk ⊢
      have := checkRow_ok b b c c hb hb row hc.1 k hk
      rw [pow_zero, one_nsmul, succ_nsmul]
      exact this
    | succ j =>
      rw [List.getD_cons_succ] at hk ⊢
      have := ih (pointMul 256 b) ((256 : Nat) • c) (pointMul_rep 256 hb) hc.2 j
        (by simp only [List.length_cons] at hj; omega) hk
      rw [smul_smul, smul_smul] at this
      rw [smul_smul, pow_succ, ← Nat.mul_assoc]
      exact this

private theorem tables_check : checkTables basePoint baseRows = true := by decide +kernel

private theorem tables_length :
    baseRows.length = 56 ∧ baseRows.all (fun row => row.length == 8) = true := by decide +kernel

/-- Entry `k ≤ 8` of table `j < 56` is `[k 256^j] B`, affine. -/
theorem baseTable_ok (j k : Nat) (hj : j < 56) (hk : k < 9) :
    Rep (basePt (baseTable j k)) ((k * 256 ^ j) • baseAff) := by
  cases k with
  | zero =>
    rw [Nat.zero_mul, zero_smul]
    exact identity_rep
  | succ k =>
    have hrow : (baseRows.getD j []) ∈ baseRows := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [tables_length.1]; exact hj)]
      exact List.getElem_mem _
    have hlen : (baseRows.getD j []).length = 8 :=
      beq_iff_eq.mp (List.all_eq_true.mp tables_length.2 _ hrow)
    have hr := checkTables_ok basePoint baseAff basePoint_rep _ tables_check j
      (by rw [tables_length.1]; exact hj) k (by rw [hlen]; omega)
    simp only [baseTable, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    rw [smul_smul] at hr
    exact hr

/-- The constant the digits are offset by: `8 Σ_{j < 56} 256^j`. -/
def baseGVal : Nat := 8 * ((256 ^ 56 - 1) / 255)

private def baseGCheck (p : Point) : Bool :=
  baseG.1 * p.Z == p.X && baseG.2 * p.Z == p.Y && p.Z != 0

private theorem baseG_check : baseGCheck (pointMul baseGVal basePoint) = true := by decide +kernel

theorem baseG_ok : Rep (basePt baseG) (baseGVal • baseAff) := by
  have hp := pointMul_rep baseGVal basePoint_rep
  have hc := baseG_check
  simp only [baseGCheck, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hc
  obtain ⟨⟨hx, hy⟩, _⟩ := hc
  exact basePt_rep hp hx hy

end VG.Proof.X448
