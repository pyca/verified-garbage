module

-- separate module: its proofs (about 7 s, the limbs' arithmetic) are not checked again when `Glue` changes

public import VerifiedGarbage.Proof.Framework.PowLit

/-!
# P-256 on x86-64 with AVX512_IFMA: the arithmetic of the lanes

A field element is five signed limbs `x₀ + 2⁵² x₁ + … + 2²⁰⁸ x₄` (`val5`),
standing for its residue modulo `p`, in Montgomery form with `R = 2²⁶⁰`.
-/

@[expose] public section

namespace VG.Proof.P256.X86_64.Ifma

/-- The prime of P-256. -/
def pI : Int := 2 ^ 256 - 2 ^ 224 + 2 ^ 192 + 2 ^ 96 - 1

/-- The number five limbs stand for. -/
def val5 (v0 v1 v2 v3 v4 : Int) : Int := v0 + v1 * 2 ^ 52 + v2 * 2 ^ 104 + v3 * 2 ^ 156 + v4 * 2 ^ 208

/-! ## `norm`: the top limb's bits from 48 up folded, then a signed carry -/

/-- The limbs after `norm`. -/
def normI (v0 v1 v2 v3 v4 : Int) : Int × Int × Int × Int × Int :=
  let h := v4 / 2 ^ 48
  let x0 := v0 + h
  let x1 := v1 - h * 2 ^ 44
  let x3 := v3 - h * 2 ^ 36
  let x4 := v4 % 2 ^ 48 + h * 2 ^ 16
  let y1 := x1 + x0 / 2 ^ 52
  let y2 := v2 + y1 / 2 ^ 52
  let y3 := x3 + y2 / 2 ^ 52
  (x0 % 2 ^ 52, y1 % 2 ^ 52, y2 % 2 ^ 52, y3 % 2 ^ 52, x4 + y3 / 2 ^ 52)

/-- `norm` subtracts a multiple of `p`. -/
theorem normI_val (v0 v1 v2 v3 v4 : Int) :
    let o := normI v0 v1 v2 v3 v4
    val5 o.1 o.2.1 o.2.2.1 o.2.2.2.1 o.2.2.2.2 = val5 v0 v1 v2 v3 v4 - v4 / 2 ^ 48 * pI := by
  simp only [normI, val5, pI]
  omega

/-- The limbs after `norm` are below `2⁵²`, of a number in `[0, 2²⁶⁰)`. -/
theorem normI_lt {v0 v1 v2 v3 v4 : Int} (h0 : -2 ^ 63 ≤ v0) (h1 : -2 ^ 63 ≤ v1) (h2 : -2 ^ 63 ≤ v2)
    (h3 : -2 ^ 63 ≤ v3) (g0 : v0 < 2 ^ 63) (g1 : v1 < 2 ^ 63) (g2 : v2 < 2 ^ 63) (g3 : v3 < 2 ^ 63)
    (hv : 0 ≤ val5 v0 v1 v2 v3 v4) (gv : val5 v0 v1 v2 v3 v4 < 2 ^ 260) :
    let o := normI v0 v1 v2 v3 v4
    (0 ≤ o.1 ∧ o.1 < 2 ^ 52) ∧ (0 ≤ o.2.1 ∧ o.2.1 < 2 ^ 52) ∧ (0 ≤ o.2.2.1 ∧ o.2.2.1 < 2 ^ 52) ∧
      (0 ≤ o.2.2.2.1 ∧ o.2.2.2.1 < 2 ^ 52) ∧ (0 ≤ o.2.2.2.2 ∧ o.2.2.2.2 < 2 ^ 49) := by
  simp only [normI, val5] at *
  omega

/-- `norm` of a number in `[0, 2²⁶⁸)`, where what its last carry is taken
from is within 64 signed bits: carried limbs, of the number less a multiple of `p`,
below `2²⁵⁶ + 2²³⁸`. -/
theorem normI_carried {v0 v1 v2 v3 v4 : Int}
    (r3 : -2 ^ 63 ≤ v3 - v4 / 2 ^ 48 * 2 ^ 36 +
        (v2 + (v1 - v4 / 2 ^ 48 * 2 ^ 44 + (v0 + v4 / 2 ^ 48) / 2 ^ 52) / 2 ^ 52) / 2 ^ 52 ∧
      v3 - v4 / 2 ^ 48 * 2 ^ 36 +
        (v2 + (v1 - v4 / 2 ^ 48 * 2 ^ 44 + (v0 + v4 / 2 ^ 48) / 2 ^ 52) / 2 ^ 52) / 2 ^ 52 < 2 ^ 63)
    (hv : 0 ≤ val5 v0 v1 v2 v3 v4) (gv : val5 v0 v1 v2 v3 v4 < 2 ^ 268) :
    let o := normI v0 v1 v2 v3 v4
    ((0 ≤ o.1 ∧ o.1 < 2 ^ 52) ∧ (0 ≤ o.2.1 ∧ o.2.1 < 2 ^ 52) ∧ (0 ≤ o.2.2.1 ∧ o.2.2.1 < 2 ^ 52) ∧
      (0 ≤ o.2.2.2.1 ∧ o.2.2.2.1 < 2 ^ 52) ∧ (0 ≤ o.2.2.2.2 ∧ o.2.2.2.2 < 2 ^ 52)) ∧
      val5 o.1 o.2.1 o.2.2.1 o.2.2.2.1 o.2.2.2.2 = val5 v0 v1 v2 v3 v4 - v4 / 2 ^ 48 * pI ∧
      0 ≤ val5 o.1 o.2.1 o.2.2.1 o.2.2.2.1 o.2.2.2.2 ∧
      val5 o.1 o.2.1 o.2.2.1 o.2.2.2.1 o.2.2.2.2 < 2 ^ 256 + 2 ^ 238 := by
  simp only [normI, val5, pI] at *
  omega

/-! ## The Montgomery reduction, a limb at a time -/

/-- The low and the high 52 bits of a product of 52-bit numbers, as `vpmadd52luq` and `vpmadd52huq` add them. -/
def lo52 (a b : Int) : Int := a % 2 ^ 52 * (b % 2 ^ 52) % 2 ^ 52
def hi52 (a b : Int) : Int := a % 2 ^ 52 * (b % 2 ^ 52) / 2 ^ 52

theorem lo52_add_hi52 {a b : Int} (ha : 0 ≤ a) (ga : a < 2 ^ 52) (hb : 0 ≤ b) (gb : b < 2 ^ 52) :
    lo52 a b + hi52 a b * 2 ^ 52 = a * b := by
  unfold lo52 hi52
  rw [Int.emod_eq_of_lt ha ga, Int.emod_eq_of_lt hb gb]
  generalize a * b = q
  omega

/-- A step of the reduction: `m = t₀ mod 2⁵²` times `p` added, which leaves a
multiple of `2⁵²`. -/
theorem mont_step (t0 t1 t2 t3 t4 t5 : Int) :
    let m := t0 % 2 ^ 52
    (t1 + t0 / 2 ^ 52 + m * 2 ^ 44 % 2 ^ 52 + (t2 + m / 2 ^ 8) * 2 ^ 52 + (t3 + lo52 m (2 ^ 36)) * 2 ^ 104 +
        (t4 + hi52 m (2 ^ 36) + lo52 m (2 ^ 48 - 2 ^ 16)) * 2 ^ 156 + (t5 + hi52 m (2 ^ 48 - 2 ^ 16)) * 2 ^ 208) * 2 ^ 52 =
      t0 + t1 * 2 ^ 52 + t2 * 2 ^ 104 + t3 * 2 ^ 156 + t4 * 2 ^ 208 + t5 * 2 ^ 260 + m * pI := by
  simp only [lo52, hi52, pI]
  omega

/-- A step of the reduction on the columns `t`, at column `i`. -/
def redI (t : List Int) (i : Nat) : List Int :=
  let ti := t.getD i 0
  let m := ti % 2 ^ 52
  let t := t.set (i + 1) (t.getD (i + 1) 0 + ti / 2 ^ 52 + ti * 2 ^ 56 % 2 ^ 64 / 2 ^ 12)
  let t := t.set (i + 2) (t.getD (i + 2) 0 + m / 2 ^ 8)
  let t := t.set (i + 3) (t.getD (i + 3) 0 + lo52 ti (2 ^ 36))
  let t := t.set (i + 4) (t.getD (i + 4) 0 + hi52 ti (2 ^ 36) + lo52 ti (2 ^ 48 - 2 ^ 16))
  t.set (i + 5) (t.getD (i + 5) 0 + hi52 ti (2 ^ 48 - 2 ^ 16))

/-- The number ten columns stand for. -/
def val10 (t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 : Int) : Int :=
  t0 + t1 * 2 ^ 52 + t2 * 2 ^ 104 + t3 * 2 ^ 156 + t4 * 2 ^ 208 + t5 * 2 ^ 260 + t6 * 2 ^ 312 + t7 * 2 ^ 364 +
    t8 * 2 ^ 416 + t9 * 2 ^ 468

/-- The five steps of the reduction: the columns 5 to 9 after them. -/
def reduceI (t : List Int) : Int × Int × Int × Int × Int :=
  let t := redI (redI (redI (redI (redI t 0) 1) 2) 3) 4
  (t.getD 5 0, t.getD 6 0, t.getD 7 0, t.getD 8 0, t.getD 9 0)

/-- A step of the reduction at column `i`, on ten columns: the five after it change, and with `m p` added
(`m` the low 52 bits of column `i`) the columns from `i` are `2⁵²` times the columns after it. -/
theorem red0 (t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 : Int) :
    ∃ m u1 u2 u3 u4 u5, 0 ≤ m ∧ m < 2 ^ 52 ∧ redI [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9] 0 = [t0, u1, u2, u3, u4, u5, t6, t7, t8, t9] ∧
      (u1 + u2 * 2 ^ 52 + u3 * 2 ^ 104 + u4 * 2 ^ 156 + u5 * 2 ^ 208) * 2 ^ 52 = t0 + t1 * 2 ^ 52 + t2 * 2 ^ 104 + t3 * 2 ^ 156 + t4 * 2 ^ 208 + t5 * 2 ^ 260 + m * pI := by
  refine ⟨t0 % 2 ^ 52, t1 + t0 / 2 ^ 52 + t0 * 2 ^ 56 % 2 ^ 64 / 2 ^ 12, t2 + t0 % 2 ^ 52 / 2 ^ 8,
    t3 + lo52 t0 (2 ^ 36), t4 + hi52 t0 (2 ^ 36) + lo52 t0 (2 ^ 48 - 2 ^ 16),
    t5 + hi52 t0 (2 ^ 48 - 2 ^ 16), Int.emod_nonneg _ (by decide), Int.emod_lt_of_pos _ (by decide), ?_, ?_⟩
  · simp only [redI, List.getD_cons_zero, List.getD_cons_succ, List.set_cons_zero, List.set_cons_succ]
  · simp only [lo52, hi52, pI]
    omega

theorem red1 (t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 : Int) :
    ∃ m u1 u2 u3 u4 u5, 0 ≤ m ∧ m < 2 ^ 52 ∧ redI [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9] 1 = [t0, t1, u1, u2, u3, u4, u5, t7, t8, t9] ∧
      (u1 + u2 * 2 ^ 52 + u3 * 2 ^ 104 + u4 * 2 ^ 156 + u5 * 2 ^ 208) * 2 ^ 52 = t1 + t2 * 2 ^ 52 + t3 * 2 ^ 104 + t4 * 2 ^ 156 + t5 * 2 ^ 208 + t6 * 2 ^ 260 + m * pI := by
  refine ⟨t1 % 2 ^ 52, t2 + t1 / 2 ^ 52 + t1 * 2 ^ 56 % 2 ^ 64 / 2 ^ 12, t3 + t1 % 2 ^ 52 / 2 ^ 8,
    t4 + lo52 t1 (2 ^ 36), t5 + hi52 t1 (2 ^ 36) + lo52 t1 (2 ^ 48 - 2 ^ 16),
    t6 + hi52 t1 (2 ^ 48 - 2 ^ 16), Int.emod_nonneg _ (by decide), Int.emod_lt_of_pos _ (by decide), ?_, ?_⟩
  · simp only [redI, List.getD_cons_zero, List.getD_cons_succ, List.set_cons_zero, List.set_cons_succ]
  · simp only [lo52, hi52, pI]
    omega

theorem red2 (t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 : Int) :
    ∃ m u1 u2 u3 u4 u5, 0 ≤ m ∧ m < 2 ^ 52 ∧ redI [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9] 2 = [t0, t1, t2, u1, u2, u3, u4, u5, t8, t9] ∧
      (u1 + u2 * 2 ^ 52 + u3 * 2 ^ 104 + u4 * 2 ^ 156 + u5 * 2 ^ 208) * 2 ^ 52 = t2 + t3 * 2 ^ 52 + t4 * 2 ^ 104 + t5 * 2 ^ 156 + t6 * 2 ^ 208 + t7 * 2 ^ 260 + m * pI := by
  refine ⟨t2 % 2 ^ 52, t3 + t2 / 2 ^ 52 + t2 * 2 ^ 56 % 2 ^ 64 / 2 ^ 12, t4 + t2 % 2 ^ 52 / 2 ^ 8,
    t5 + lo52 t2 (2 ^ 36), t6 + hi52 t2 (2 ^ 36) + lo52 t2 (2 ^ 48 - 2 ^ 16),
    t7 + hi52 t2 (2 ^ 48 - 2 ^ 16), Int.emod_nonneg _ (by decide), Int.emod_lt_of_pos _ (by decide), ?_, ?_⟩
  · simp only [redI, List.getD_cons_zero, List.getD_cons_succ, List.set_cons_zero, List.set_cons_succ]
  · simp only [lo52, hi52, pI]
    omega

theorem red3 (t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 : Int) :
    ∃ m u1 u2 u3 u4 u5, 0 ≤ m ∧ m < 2 ^ 52 ∧ redI [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9] 3 = [t0, t1, t2, t3, u1, u2, u3, u4, u5, t9] ∧
      (u1 + u2 * 2 ^ 52 + u3 * 2 ^ 104 + u4 * 2 ^ 156 + u5 * 2 ^ 208) * 2 ^ 52 = t3 + t4 * 2 ^ 52 + t5 * 2 ^ 104 + t6 * 2 ^ 156 + t7 * 2 ^ 208 + t8 * 2 ^ 260 + m * pI := by
  refine ⟨t3 % 2 ^ 52, t4 + t3 / 2 ^ 52 + t3 * 2 ^ 56 % 2 ^ 64 / 2 ^ 12, t5 + t3 % 2 ^ 52 / 2 ^ 8,
    t6 + lo52 t3 (2 ^ 36), t7 + hi52 t3 (2 ^ 36) + lo52 t3 (2 ^ 48 - 2 ^ 16),
    t8 + hi52 t3 (2 ^ 48 - 2 ^ 16), Int.emod_nonneg _ (by decide), Int.emod_lt_of_pos _ (by decide), ?_, ?_⟩
  · simp only [redI, List.getD_cons_zero, List.getD_cons_succ, List.set_cons_zero, List.set_cons_succ]
  · simp only [lo52, hi52, pI]
    omega

theorem red4 (t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 : Int) :
    ∃ m u1 u2 u3 u4 u5, 0 ≤ m ∧ m < 2 ^ 52 ∧ redI [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9] 4 = [t0, t1, t2, t3, t4, u1, u2, u3, u4, u5] ∧
      (u1 + u2 * 2 ^ 52 + u3 * 2 ^ 104 + u4 * 2 ^ 156 + u5 * 2 ^ 208) * 2 ^ 52 = t4 + t5 * 2 ^ 52 + t6 * 2 ^ 104 + t7 * 2 ^ 156 + t8 * 2 ^ 208 + t9 * 2 ^ 260 + m * pI := by
  refine ⟨t4 % 2 ^ 52, t5 + t4 / 2 ^ 52 + t4 * 2 ^ 56 % 2 ^ 64 / 2 ^ 12, t6 + t4 % 2 ^ 52 / 2 ^ 8,
    t7 + lo52 t4 (2 ^ 36), t8 + hi52 t4 (2 ^ 36) + lo52 t4 (2 ^ 48 - 2 ^ 16),
    t9 + hi52 t4 (2 ^ 48 - 2 ^ 16), Int.emod_nonneg _ (by decide), Int.emod_lt_of_pos _ (by decide), ?_, ?_⟩
  · simp only [redI, List.getD_cons_zero, List.getD_cons_succ, List.set_cons_zero, List.set_cons_succ]
  · simp only [lo52, hi52, pI]
    omega

/-- The reduction divides by `2²⁶⁰` modulo `p`: it adds `M p`, `M < 2²⁶⁰`. -/
theorem reduceI_val (t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 : Int) :
    let o := reduceI [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9]
    ∃ M, 0 ≤ M ∧ M < 2 ^ 260 ∧
      val5 o.1 o.2.1 o.2.2.1 o.2.2.2.1 o.2.2.2.2 * 2 ^ 260 = val10 t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 + M * pI := by
  obtain ⟨m0, a1, a2, a3, a4, a5, h0, g0, e0, v0⟩ := red0 t0 t1 t2 t3 t4 t5 t6 t7 t8 t9
  obtain ⟨m1, b2, b3, b4, b5, b6, h1, g1, e1, v1⟩ := red1 t0 a1 a2 a3 a4 a5 t6 t7 t8 t9
  obtain ⟨m2, c3, c4, c5, c6, c7, h2, g2, e2, v2⟩ := red2 t0 a1 b2 b3 b4 b5 b6 t7 t8 t9
  obtain ⟨m3, d4, d5, d6, d7, d8, h3, g3, e3, v3⟩ := red3 t0 a1 b2 c3 c4 c5 c6 c7 t8 t9
  obtain ⟨m4, f5, f6, f7, f8, f9, h4, g4, e4, v4⟩ := red4 t0 a1 b2 c3 d4 d5 d6 d7 d8 t9
  refine ⟨m0 + m1 * 2 ^ 52 + m2 * 2 ^ 104 + m3 * 2 ^ 156 + m4 * 2 ^ 208, by omega, by omega, ?_⟩
  simp only [reduceI, e0, e1, e2, e3, e4, List.getD_cons_zero, List.getD_cons_succ, val5, val10]
  simp only [pI] at *
  omega

/-- The columns of a product, as integers. -/
def mulColsI (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : Int) : List Int :=
  [0 + lo52 a0 b0,
    ((0 + hi52 a0 b0) + lo52 a1 b0) + lo52 a0 b1,
    (((0 + hi52 a1 b0) + lo52 a1 b1) + lo52 a0 b2) + ((0 + hi52 a0 b1) + lo52 a2 b0),
    ((((0 + hi52 a1 b1) + lo52 a2 b1) + lo52 a0 b3) + ((0 + hi52 a2 b0) + lo52 a1 b2)) + ((0 + hi52 a0 b2) + lo52 a3 b0),
    ((((0 + hi52 a2 b1) + hi52 a3 b0) + lo52 a1 b3) + (((0 + hi52 a1 b2) + hi52 a0 b3) + lo52 a4 b0)) + (((0 + lo52 a2 b2) + lo52 a3 b1) + lo52 a0 b4),
    ((((0 + hi52 a2 b2) + lo52 a3 b2) + hi52 a0 b4) + (((0 + hi52 a3 b1) + lo52 a2 b3) + lo52 a4 b1)) + (((0 + hi52 a1 b3) + hi52 a4 b0) + lo52 a1 b4),
    ((((0 + hi52 a3 b2) + hi52 a4 b1) + lo52 a2 b4) + ((0 + hi52 a2 b3) + hi52 a1 b4)) + ((0 + lo52 a3 b3) + lo52 a4 b2),
    (((0 + hi52 a3 b3) + hi52 a2 b4) + lo52 a3 b4) + ((0 + hi52 a4 b2) + lo52 a4 b3),
    ((0 + hi52 a4 b3) + hi52 a3 b4) + lo52 a4 b4,
    0 + hi52 a4 b4]

/-- The columns of a square, as integers. -/
def sqrColsI (a0 a1 a2 a3 a4 : Int) : List Int :=
  [0 + lo52 a0 a0,
    ((0 + lo52 a0 a1) + (0 + lo52 a0 a1)) + hi52 a0 a0,
    (((0 + hi52 a0 a1) + lo52 a0 a2) + ((0 + hi52 a0 a1) + lo52 a0 a2)) + lo52 a1 a1,
    ((((0 + hi52 a0 a2) + lo52 a1 a2) + lo52 a0 a3) + (((0 + hi52 a0 a2) + lo52 a1 a2) + lo52 a0 a3)) + hi52 a1 a1,
    ((((0 + hi52 a1 a2) + lo52 a1 a3) + ((0 + hi52 a0 a3) + lo52 a0 a4)) + (((0 + hi52 a1 a2) + lo52 a1 a3) + ((0 + hi52 a0 a3) + lo52 a0 a4))) + lo52 a2 a2,
    ((((0 + hi52 a1 a3) + hi52 a0 a4) + ((0 + lo52 a2 a3) + lo52 a1 a4)) + (((0 + hi52 a1 a3) + hi52 a0 a4) + ((0 + lo52 a2 a3) + lo52 a1 a4))) + hi52 a2 a2,
    ((((0 + hi52 a2 a3) + hi52 a1 a4) + lo52 a2 a4) + (((0 + hi52 a2 a3) + hi52 a1 a4) + lo52 a2 a4)) + lo52 a3 a3,
    (((0 + hi52 a2 a4) + lo52 a3 a4) + ((0 + hi52 a2 a4) + lo52 a3 a4)) + hi52 a3 a3,
    ((0 + hi52 a3 a4) + (0 + hi52 a3 a4)) + lo52 a4 a4,
    0 + hi52 a4 a4]

/-- The number the ten columns of a list stand for. -/
def val10L (t : List Int) : Int :=
  val10 (t.getD 0 0) (t.getD 1 0) (t.getD 2 0) (t.getD 3 0) (t.getD 4 0) (t.getD 5 0) (t.getD 6 0) (t.getD 7 0)
    (t.getD 8 0) (t.getD 9 0)

theorem val5_mul (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : Int) :
    val5 a0 a1 a2 a3 a4 * val5 b0 b1 b2 b3 b4 =
      a0 * b0 + a0 * b1 * 2 ^ 52 + a0 * b2 * 2 ^ 104 + a0 * b3 * 2 ^ 156 + a0 * b4 * 2 ^ 208 + a1 * b0 * 2 ^ 52 + a1 * b1 * 2 ^ 104 + a1 * b2 * 2 ^ 156 + a1 * b3 * 2 ^ 208 + a1 * b4 * 2 ^ 260 + a2 * b0 * 2 ^ 104 + a2 * b1 * 2 ^ 156 + a2 * b2 * 2 ^ 208 + a2 * b3 * 2 ^ 260 + a2 * b4 * 2 ^ 312 + a3 * b0 * 2 ^ 156 + a3 * b1 * 2 ^ 208 + a3 * b2 * 2 ^ 260 + a3 * b3 * 2 ^ 312 + a3 * b4 * 2 ^ 364 + a4 * b0 * 2 ^ 208 + a4 * b1 * 2 ^ 260 + a4 * b2 * 2 ^ 312 + a4 * b3 * 2 ^ 364 + a4 * b4 * 2 ^ 416 := by
  simp only [val5]
  grind

/-- The columns of a product stand for the product. -/
theorem mulColsI_val {a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : Int} (ha0 : 0 ≤ a0 ∧ a0 < 2 ^ 52) (ha1 : 0 ≤ a1 ∧ a1 < 2 ^ 52) (ha2 : 0 ≤ a2 ∧ a2 < 2 ^ 52) (ha3 : 0 ≤ a3 ∧ a3 < 2 ^ 52) (ha4 : 0 ≤ a4 ∧ a4 < 2 ^ 52)
    (hb0 : 0 ≤ b0 ∧ b0 < 2 ^ 52) (hb1 : 0 ≤ b1 ∧ b1 < 2 ^ 52) (hb2 : 0 ≤ b2 ∧ b2 < 2 ^ 52) (hb3 : 0 ≤ b3 ∧ b3 < 2 ^ 52) (hb4 : 0 ≤ b4 ∧ b4 < 2 ^ 52) :
    val10L (mulColsI a0 a1 a2 a3 a4 b0 b1 b2 b3 b4) = val5 a0 a1 a2 a3 a4 * val5 b0 b1 b2 b3 b4 := by
  have h00 := lo52_add_hi52 (ha0).1 (ha0).2 (hb0).1 (hb0).2
  have h01 := lo52_add_hi52 (ha0).1 (ha0).2 (hb1).1 (hb1).2
  have h02 := lo52_add_hi52 (ha0).1 (ha0).2 (hb2).1 (hb2).2
  have h03 := lo52_add_hi52 (ha0).1 (ha0).2 (hb3).1 (hb3).2
  have h04 := lo52_add_hi52 (ha0).1 (ha0).2 (hb4).1 (hb4).2
  have h10 := lo52_add_hi52 (ha1).1 (ha1).2 (hb0).1 (hb0).2
  have h11 := lo52_add_hi52 (ha1).1 (ha1).2 (hb1).1 (hb1).2
  have h12 := lo52_add_hi52 (ha1).1 (ha1).2 (hb2).1 (hb2).2
  have h13 := lo52_add_hi52 (ha1).1 (ha1).2 (hb3).1 (hb3).2
  have h14 := lo52_add_hi52 (ha1).1 (ha1).2 (hb4).1 (hb4).2
  have h20 := lo52_add_hi52 (ha2).1 (ha2).2 (hb0).1 (hb0).2
  have h21 := lo52_add_hi52 (ha2).1 (ha2).2 (hb1).1 (hb1).2
  have h22 := lo52_add_hi52 (ha2).1 (ha2).2 (hb2).1 (hb2).2
  have h23 := lo52_add_hi52 (ha2).1 (ha2).2 (hb3).1 (hb3).2
  have h24 := lo52_add_hi52 (ha2).1 (ha2).2 (hb4).1 (hb4).2
  have h30 := lo52_add_hi52 (ha3).1 (ha3).2 (hb0).1 (hb0).2
  have h31 := lo52_add_hi52 (ha3).1 (ha3).2 (hb1).1 (hb1).2
  have h32 := lo52_add_hi52 (ha3).1 (ha3).2 (hb2).1 (hb2).2
  have h33 := lo52_add_hi52 (ha3).1 (ha3).2 (hb3).1 (hb3).2
  have h34 := lo52_add_hi52 (ha3).1 (ha3).2 (hb4).1 (hb4).2
  have h40 := lo52_add_hi52 (ha4).1 (ha4).2 (hb0).1 (hb0).2
  have h41 := lo52_add_hi52 (ha4).1 (ha4).2 (hb1).1 (hb1).2
  have h42 := lo52_add_hi52 (ha4).1 (ha4).2 (hb2).1 (hb2).2
  have h43 := lo52_add_hi52 (ha4).1 (ha4).2 (hb3).1 (hb3).2
  have h44 := lo52_add_hi52 (ha4).1 (ha4).2 (hb4).1 (hb4).2
  rw [val5_mul]
  simp only [val10L, mulColsI, List.getD_cons_zero, List.getD_cons_succ, val10]
  omega

/-- The columns of a square stand for the square. -/
theorem sqrColsI_val {a0 a1 a2 a3 a4 : Int} (ha0 : 0 ≤ a0 ∧ a0 < 2 ^ 52) (ha1 : 0 ≤ a1 ∧ a1 < 2 ^ 52) (ha2 : 0 ≤ a2 ∧ a2 < 2 ^ 52) (ha3 : 0 ≤ a3 ∧ a3 < 2 ^ 52) (ha4 : 0 ≤ a4 ∧ a4 < 2 ^ 52) :
    val10L (sqrColsI a0 a1 a2 a3 a4) = val5 a0 a1 a2 a3 a4 * val5 a0 a1 a2 a3 a4 := by
  have h00 := lo52_add_hi52 (ha0).1 (ha0).2 (ha0).1 (ha0).2
  have h01 := lo52_add_hi52 (ha0).1 (ha0).2 (ha1).1 (ha1).2
  have h02 := lo52_add_hi52 (ha0).1 (ha0).2 (ha2).1 (ha2).2
  have h03 := lo52_add_hi52 (ha0).1 (ha0).2 (ha3).1 (ha3).2
  have h04 := lo52_add_hi52 (ha0).1 (ha0).2 (ha4).1 (ha4).2
  have h11 := lo52_add_hi52 (ha1).1 (ha1).2 (ha1).1 (ha1).2
  have h12 := lo52_add_hi52 (ha1).1 (ha1).2 (ha2).1 (ha2).2
  have h13 := lo52_add_hi52 (ha1).1 (ha1).2 (ha3).1 (ha3).2
  have h14 := lo52_add_hi52 (ha1).1 (ha1).2 (ha4).1 (ha4).2
  have h22 := lo52_add_hi52 (ha2).1 (ha2).2 (ha2).1 (ha2).2
  have h23 := lo52_add_hi52 (ha2).1 (ha2).2 (ha3).1 (ha3).2
  have h24 := lo52_add_hi52 (ha2).1 (ha2).2 (ha4).1 (ha4).2
  have h33 := lo52_add_hi52 (ha3).1 (ha3).2 (ha3).1 (ha3).2
  have h34 := lo52_add_hi52 (ha3).1 (ha3).2 (ha4).1 (ha4).2
  have h44 := lo52_add_hi52 (ha4).1 (ha4).2 (ha4).1 (ha4).2
  rw [val5_mul]
  simp only [val10L, sqrColsI, List.getD_cons_zero, List.getD_cons_succ, val10]
  have c (x y : Int) : y * x = x * y := Int.mul_comm y x
  rw [c a0 a1, c a0 a2, c a0 a3, c a0 a4, c a1 a2, c a1 a3, c a1 a4, c a2 a3, c a2 a4, c a3 a4]
  omega

end VG.Proof.P256.X86_64.Ifma
