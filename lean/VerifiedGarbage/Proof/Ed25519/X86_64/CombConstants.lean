import VerifiedGarbage.Proof.Ed25519.WindowConstants
import VerifiedGarbage.Proof.Ed25519.X86_64.CombSelect

/-!
# The comb's tables represent `[k 1024^j]B`, `combG` represents `[G]B`, and `combStart` `[G']B`

Each entry is turned back into affine `(x, y)` (`uncache`, which the kernel
checks inverts the caching) and `checkTables` walks the tables once: within
table `j`, each entry is the previous one plus the first, with the
specification's addition, compared projectively; the first entry of table `j +
1` is `[1024]` of table `j`'s, with the specification's `pointMul`. `combG` and
`combStart b` are compared with `pointMul` of the base point, and `[32]` of the
start with `[W b]B` (`combStart_32`), `W b = 33 G + 32^51 (b - 16)`: the start is
`W b / 32` modulo the group's order.
-/

namespace VG.Proof.Ed25519.X86_64

open VG.Spec.Ed25519 VG.Impl.Ed25519.X86_64 VG.Proof.Ed25519 Edwards
open Spec.X25519 (Fe)

/-- `1/2`. -/
def half : Fe := ⟨(Spec.X25519.P + 1) / 2, by decide⟩

/-- The affine `(x, y)` of a cached entry `[y - x, y + x, 2dxy]` with `Z = 1`. -/
def uncache (e : Fe × Fe × Fe) : Fe × Fe := ((e.2.1 - e.1) * half, (e.2.1 + e.1) * half)

/-- The entries `p`, `p + b`, `p + 2b`, …, each compared with `p`'s representative. -/
private def checkRow (b p : Point) : List (Fe × Fe) → Bool
  | [] => true
  | q :: qs => (q.1 * p.Z == p.X && q.2 * p.Z == p.Y && p.Z != 0) &&
      checkRow b (pointAdd (affPt q) b) qs

private theorem checkRow_ok (b p : Point) (c a : EPoint dZ) (hb : Rep b c) (h : Rep p a)
    (qs : List (Fe × Fe)) (hc : checkRow b p qs = true) (i : Nat) (hi : i < qs.length) :
    Rep (affPt (qs.getD i (0, 1))) (i • c + a) := by
  induction qs generalizing p a i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons q qs ih =>
    simp only [checkRow, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hc
    obtain ⟨⟨⟨hx, hy⟩, hz⟩, hrest⟩ := hc
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
      have := ih _ _ (pointAdd_rep hq hb) hrest i (by simp only [List.length_cons] at hi; omega)
      rw [List.getD_cons_succ]
      convert this using 1
      rw [succ_nsmul]; abel

/-- Each table checked from the representative `b` of its first entry. -/
private def checkTables (b : Point) : List (List (Fe × Fe)) → Bool
  | [] => true
  | row :: rows => checkRow b b row && checkTables (pointMul 1024 b) rows

private theorem checkTables_ok (b : Point) (c : EPoint dZ) (hb : Rep b c)
    (rows : List (List (Fe × Fe))) (hc : checkTables b rows = true) (j : Nat) (hj : j < rows.length)
    (k : Nat) (hk : k < (rows.getD j []).length) :
    Rep (affPt ((rows.getD j []).getD k (0, 1))) ((k + 1) • ((1024 ^ j) • c)) := by
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
      have := ih (pointMul 1024 b) ((1024 : Nat) • c) (pointMul_rep 1024 hb) hc.2 j
        (by simp only [List.length_cons] at hj; omega) hk
      rw [smul_smul, smul_smul] at this
      rw [smul_smul, pow_succ, ← Nat.mul_assoc]
      exact this

private theorem tables_check :
    checkTables basePoint (combTable.map (·.map uncache)) = true := by decide +kernel

/-- The caching of `affPt (uncache e)`. -/
private def recache (e : Fe × Fe × Fe) : Fe × Fe × Fe :=
  ((uncache e).2 - (uncache e).1, (uncache e).2 + (uncache e).1,
    (uncache e).1 * (uncache e).2 * 2 * d)

private theorem tables_cached :
    combTable.all (fun row => row.all fun e => decide (recache e = e)) = true := by decide +kernel

private theorem getD_map' {α β : Type} (l : List α) (f : α → β) (n : Nat) (d : α) :
    (l.map f).getD n (f d) = f (l.getD n d) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, Option.getD_map]

private theorem uncache_default : uncache (1, 1, 0) = (0, 1) := by decide

theorem combCached_ok (j k : Nat) (hj : j < 26) (hk : k < 17) :
    ∃ q, combCached j k = cache q ∧ Rep q ((k * 1024 ^ j) • baseAff) := by
  cases k with
  | zero =>
    refine ⟨identity, ?_, ?_⟩
    · simp only [combCached, ↓reduceIte]; decide +kernel
    · rw [Nat.zero_mul, zero_smul]; exact identity_rep
  | succ k =>
    have hrow : (combTable.getD j []) ∈ combTable := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [tables_length.1]; exact hj)]
      exact List.getElem_mem _
    have hlen : (combTable.getD j []).length = 16 :=
      beq_iff_eq.mp (List.all_eq_true.mp tables_length.2 _ hrow)
    have hmem : (combTable.getD j []).getD k (1, 1, 0) ∈ combTable.getD j [] := by
      have hk' : k < (combTable.getD j []).length := by rw [hlen]; omega
      rw [List.getD_eq_getElem?_getD (l := combTable.getD j []), List.getElem?_eq_getElem hk']
      exact List.getElem_mem _
    have hre := of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp tables_cached _ hrow) _ hmem)
    refine ⟨affPt (uncache ((combTable.getD j []).getD k (1, 1, 0))), ?_, ?_⟩
    · simp only [combCached, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      generalize (combTable.getD j []).getD k (1, 1, 0) = e at hre
      obtain ⟨a, b, c⟩ := e
      simp only [recache, Prod.mk.injEq] at hre
      simp only [cache, affPt, Point.mk.injEq]
      exact ⟨hre.1.symm, hre.2.1.symm, hre.2.2.symm, rfl⟩
    · have hgj : (combTable.map (·.map uncache)).getD j [] = (combTable.getD j []).map uncache := by
        rw [show ([] : List (Fe × Fe)) = ([] : List (Fe × Fe × Fe)).map uncache from rfl, getD_map']
      have hr := checkTables_ok basePoint baseAff basePoint_rep _ tables_check j
        (by rw [List.length_map, tables_length.1]; exact hj) k
        (by rw [hgj, List.length_map, hlen]; omega)
      rw [hgj, ← uncache_default, getD_map', smul_smul] at hr
      exact hr

/-- The constant the comb's digits are offset by: `16 Σ_{j < 26} 1024^j`. -/
def combGVal : Nat := 16 * ((1024 ^ 26 - 1) / 1023)

private def combGCheck (p : Point) : Bool := combG.X * p.Z == p.X && combG.Y * p.Z == p.Y && p.Z != 0

private theorem combG_check : combGCheck (pointMul combGVal basePoint) = true := by decide +kernel

theorem combG_ok : Rep combG (combGVal • baseAff) := by
  have hp := pointMul_rep combGVal basePoint_rep
  have hc := combG_check
  simp only [combGCheck, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hc
  obtain ⟨⟨hx, hy⟩, _⟩ := hc
  refine hp.of_proj (show toZ 1 ≠ 0 by decide) ?_ ?_ ?_
  · show toZ combG.X * toZ _ = toZ _ * toZ 1
    rw [toZ_one, mul_one, ← toZ_mul, hx]
  · show toZ combG.Y * toZ _ = toZ _ * toZ 1
    rw [toZ_one, mul_one, ← toZ_mul, hy]
  · show toZ (combGAff.1 * combGAff.2) * toZ 1 = toZ combGAff.1 * toZ combGAff.2
    rw [toZ_mul, toZ_one, mul_one]

theorem combGCached_eq : combGCached = cache combG := by decide +kernel

/-- The multiple of `B` the comb starts at, for bit 255 `b`: `(W b) / 32` modulo the group's order
(`combStartW`), so that its five doublings give `[W b]B`. -/
def combStartVal (b : Bool) : Nat :=
  if b then 6361561354267875655831268833642632034291304792232850229338932348362443402247
  else 4552309959934810102337972192881883474083961281832216416222407598238800751623

/-- `33 G + 32 (b - 16) 1024^25`: the offset `33 G` of the digits, and `32^51` times the top
chunk's digit, `b - 16`. -/
def combStartW (b : Bool) : Nat := 33 * combGVal + 32 * (if b then 1 else 0) * 1024 ^ 25 - 512 * 1024 ^ 25

private def combStartCheck (b : Bool) (p : Point) : Bool :=
  (combStart b).X * p.Z == p.X && (combStart b).Y * p.Z == p.Y && p.Z != 0

private theorem combStart_check : ∀ b, combStartCheck b (pointMul (combStartVal b) basePoint) = true := by
  decide +kernel

theorem combStart_ok (b : Bool) : Rep (combStart b) (combStartVal b • baseAff) := by
  have hp := pointMul_rep (combStartVal b) basePoint_rep
  have hc := combStart_check b
  simp only [combStartCheck, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hc
  obtain ⟨⟨hx, hy⟩, _⟩ := hc
  refine hp.of_proj (show toZ 1 ≠ 0 by decide) ?_ ?_ ?_
  · show toZ (combStart b).X * toZ _ = toZ _ * toZ 1
    rw [toZ_one, mul_one, ← toZ_mul, hx]
  · show toZ (combStart b).Y * toZ _ = toZ _ * toZ 1
    rw [toZ_one, mul_one, ← toZ_mul, hy]
  · show toZ ((combStartAff b).1 * (combStartAff b).2) * toZ 1 = toZ (combStartAff b).1 * toZ (combStartAff b).2
    rw [toZ_mul, toZ_one, mul_one]

private theorem combStart_32_check : ∀ b,
    pointEqual (pointMul (32 * combStartVal b) basePoint) (pointMul (combStartW b) basePoint) = true := by
  decide +kernel

/-- Five doublings of the start give `[W b]B`: `32 (combStartVal b) ≡ W b` modulo the group's
order. -/
theorem combStart_32 (b : Bool) : (32 * combStartVal b) • baseAff = (combStartW b) • baseAff := by
  have hp := pointMul_rep (32 * combStartVal b) basePoint_rep
  have hq := pointMul_rep (combStartW b) basePoint_rep
  have h := combStart_32_check b
  simp only [pointEqual, Bool.and_eq_true, beq_iff_eq] at h
  have e1 := congrArg toZ h.1
  have e2 := congrArg toZ h.2
  rw [toZ_mul, toZ_mul, hp.x, hq.x] at e1
  rw [toZ_mul, toZ_mul, hp.y, hq.y] at e2
  have hz := mul_ne_zero hp.z hq.z
  ext
  · exact mul_right_cancel₀ hz (by rw [← mul_assoc, e1, mul_assoc]; exact congrArg _ (mul_comm _ _))
  · exact mul_right_cancel₀ hz (by rw [← mul_assoc, e2, mul_assoc]; exact congrArg _ (mul_comm _ _))

end VG.Proof.Ed25519.X86_64
