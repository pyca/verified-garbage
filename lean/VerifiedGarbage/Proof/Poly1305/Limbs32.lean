module

public import VerifiedGarbage.Spec.Poly1305
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Framework.Omega

/-!
# Poly1305 arithmetic in radix 2^32

Target-independent identities and bounds for an accumulator of five 32-bit
words, the top one not reduced, and a clamped key of four: its words are
`r0` and `4 q1`, `4 q2`, `4 q3` (the clamp clears the low two bits of the
upper three), and `2¹²⁸ · 4 qj ≡ 5 qj` modulo `p = 2¹³⁰ - 5`.

Every sum is a chain of steps `lo + 2³² hi = n m + c + x`, each taking the
carry `hi` of the one before, as a multiply-accumulate of two words gives
them (`n m + c + x < 2⁶⁴`).
-/
-- separate module: the arithmetic in radix 2³², target-independent, as `Limbs26` and `Limbs64` are

@[expose] public section

namespace VG.Proof.Poly1305.Limbs32
open VG.Spec.Poly1305 (P)

/-- The number of five words. -/
def val5 (x0 x1 x2 x3 x4 : Nat) : Nat := x0 + 2 ^ 32 * x1 + 2 ^ 64 * x2 + 2 ^ 96 * x3 + 2 ^ 128 * x4

/-- The clamped key of the words `r0`, `4 q1`, `4 q2`, `4 q3`. -/
def key (r0 q1 q2 q3 : Nat) : Nat := r0 + 2 ^ 32 * (4 * q1) + 2 ^ 64 * (4 * q2) + 2 ^ 96 * (4 * q3)

/-- The bound the top word keeps between blocks: five times its bits from 2
up fit a word. -/
abbrev topMax : Nat := 3 * 2 ^ 30

/-! ## Adding a block -/

/-- `a = h + m + 2¹²⁸ pad`, with `h`'s bits from 130 up folded in as five
times themselves, in a chain from the carry `5 ⌊h4 / 4⌋`: congruent to the
sum, with a top word of at most 6. -/
theorem add_arith {h0 h1 h2 h3 h4 m0 m1 m2 m3 pad a0 a1 a2 a3 c1 c2 c3 c4 : Nat}
    (hh0 : h0 < 2 ^ 32) (hh1 : h1 < 2 ^ 32) (hh2 : h2 < 2 ^ 32) (hh3 : h3 < 2 ^ 32)
    (hm0 : m0 < 2 ^ 32) (hm1 : m1 < 2 ^ 32) (hm2 : m2 < 2 ^ 32) (hm3 : m3 < 2 ^ 32) (hpad : pad ≤ 1)
    (hc : 5 * (h4 / 4) < 2 ^ 32)
    (e0 : a0 + 2 ^ 32 * c1 = h0 + 5 * (h4 / 4) + m0) (e1 : a1 + 2 ^ 32 * c2 = h1 + c1 + m1)
    (e2 : a2 + 2 ^ 32 * c3 = h2 + c2 + m2) (e3 : a3 + 2 ^ 32 * c4 = h3 + c3 + m3) :
    val5 a0 a1 a2 a3 (h4 % 4 + c4 + pad) % P =
        (val5 h0 h1 h2 h3 h4 + (m0 + 2 ^ 32 * m1 + 2 ^ 64 * m2 + 2 ^ 96 * m3) + 2 ^ 128 * pad) % P ∧
      h4 % 4 + c4 + pad ≤ 6 := by
  refine ⟨?_, by omega_using [hh0, hh1, hh2, hh3, hm0, hm1, hm2, hm3, hpad, hc, e0, e1, e2, e3]⟩
  rw [show val5 h0 h1 h2 h3 h4 + (m0 + 2 ^ 32 * m1 + 2 ^ 64 * m2 + 2 ^ 96 * m3) + 2 ^ 128 * pad =
      val5 a0 a1 a2 a3 (h4 % 4 + c4 + pad) + P * (h4 / 4) by
    simp only [val5, P]; omega_using [e0, e1, e2, e3], Nat.add_mul_mod_self_left]

/-! ## Multiplying by the key -/

/-- A chain over the four low words: what it adds to the number, when the
sum fits five words. -/
theorem chain_arith {x0 x1 x2 x3 x4 p0 p1 p2 p3 z0 z1 z2 z3 z4 c1 c2 c3 c4 : Nat}
    (e0 : z0 + 2 ^ 32 * c1 = p0 + 0 + x0) (e1 : z1 + 2 ^ 32 * c2 = p1 + c1 + x1)
    (e2 : z2 + 2 ^ 32 * c3 = p2 + c2 + x2) (e3 : z3 + 2 ^ 32 * c4 = p3 + c3 + x3)
    (e4 : z4 = (x4 + c4) % 2 ^ 32)
    (hb : val5 x0 x1 x2 x3 x4 + (p0 + 2 ^ 32 * p1 + 2 ^ 64 * p2 + 2 ^ 96 * p3) < 2 ^ 160) :
    val5 z0 z1 z2 z3 z4 = val5 x0 x1 x2 x3 x4 + (p0 + 2 ^ 32 * p1 + 2 ^ 64 * p2 + 2 ^ 96 * p3) := by
  simp only [val5] at hb ⊢
  omega_using [e0, e1, e2, e3, e4, hb]

/-- The first chain, of `r0`: the columns start from the products of `a4`,
each added as the high word of a step, and `a4 r0` is added to the top word. -/
theorem first_arith {p0 p1 p2 p3 p4 t1 t2 t3 x0 x1 x2 x3 x4 y1 y2 y3 y4 : Nat}
    (e0 : x0 + 2 ^ 32 * y1 = p0 + 0 + 0) (e1 : x1 + 2 ^ 32 * y2 = p1 + t1 + y1)
    (e2 : x2 + 2 ^ 32 * y3 = p2 + t2 + y2) (e3 : x3 + 2 ^ 32 * y4 = p3 + t3 + y3)
    (e4 : x4 = (p4 + y4) % 2 ^ 32)
    (hb : p0 + 2 ^ 32 * (p1 + t1) + 2 ^ 64 * (p2 + t2) + 2 ^ 96 * (p3 + t3) + 2 ^ 128 * p4 < 2 ^ 160) :
    val5 x0 x1 x2 x3 x4 =
      p0 + 2 ^ 32 * (p1 + t1) + 2 ^ 64 * (p2 + t2) + 2 ^ 96 * (p3 + t3) + 2 ^ 128 * p4 := by
  simp only [val5]
  omega_using [e0, e1, e2, e3, e4, hb]

/-- `(a0 + … + 2¹²⁸ a4) (r0 + 2³² 4 q1 + 2⁶⁴ 4 q2 + 2⁹⁶ 4 q3)`, as the columns
of the products the code computes and the multiple of `p` between them. -/
theorem expand (a0 a1 a2 a3 a4 r0 q1 q2 q3 : Nat) :
    val5 a0 a1 a2 a3 a4 * key r0 q1 q2 q3 =
      (a0 * r0 + a3 * (5 * q1) + a2 * (5 * q2) + a1 * (5 * q3)) +
      2 ^ 32 * (a1 * r0 + a4 * (5 * q1) + a0 * (4 * q1) + a3 * (5 * q2) + a2 * (5 * q3)) +
      2 ^ 64 * (a2 * r0 + a4 * (5 * q2) + a1 * (4 * q1) + a0 * (4 * q2) + a3 * (5 * q3)) +
      2 ^ 96 * (a3 * r0 + a4 * (5 * q3) + a2 * (4 * q1) + a1 * (4 * q2) + a0 * (4 * q3)) +
      2 ^ 128 * (a4 * r0) +
      P * (a3 * q1 + a2 * q2 + a1 * q3 + 2 ^ 32 * (a4 * q1 + a3 * q2 + a2 * q3) +
        2 ^ 64 * (a4 * q2 + a3 * q3) + 2 ^ 96 * (a4 * q3)) := by
  simp only [val5, key, P]
  grind

/-- The products of a word and a word of the key, or five quarters of one. -/
theorem prod_le {a m A M : Nat} (ha : a ≤ A) (hm : m ≤ M) : a * m ≤ A * M := Nat.mul_le_mul ha hm

/-- The product, from its four chains: the number `w` they leave is congruent
to `a r`, and its top word is below `topMax`. `x` is the number after the
first chain, `y` and `z` after the next two. -/
theorem mul_arith {a0 a1 a2 a3 a4 r0 q1 q2 q3 : Nat}
    (ha0 : a0 < 2 ^ 32) (ha1 : a1 < 2 ^ 32) (ha2 : a2 < 2 ^ 32) (ha3 : a3 < 2 ^ 32) (ha4 : a4 ≤ 6)
    (hr0 : r0 < 2 ^ 28) (hq1 : q1 < 2 ^ 26) (hq2 : q2 < 2 ^ 26) (hq3 : q3 < 2 ^ 26)
    {x0 x1 x2 x3 x4 xc1 xc2 xc3 xc4 : Nat}
    (ex0 : x0 + 2 ^ 32 * xc1 = a0 * r0 + 0 + 0) (ex1 : x1 + 2 ^ 32 * xc2 = a1 * r0 + a4 * (5 * q1) + xc1)
    (ex2 : x2 + 2 ^ 32 * xc3 = a2 * r0 + a4 * (5 * q2) + xc2)
    (ex3 : x3 + 2 ^ 32 * xc4 = a3 * r0 + a4 * (5 * q3) + xc3) (ex4 : x4 = (a4 * r0 + xc4) % 2 ^ 32)
    {y0 y1 y2 y3 y4 yc1 yc2 yc3 yc4 : Nat}
    (ey0 : y0 + 2 ^ 32 * yc1 = a3 * (5 * q1) + 0 + x0) (ey1 : y1 + 2 ^ 32 * yc2 = a0 * (4 * q1) + yc1 + x1)
    (ey2 : y2 + 2 ^ 32 * yc3 = a1 * (4 * q1) + yc2 + x2) (ey3 : y3 + 2 ^ 32 * yc4 = a2 * (4 * q1) + yc3 + x3)
    (ey4 : y4 = (x4 + yc4) % 2 ^ 32)
    {z0 z1 z2 z3 z4 zc1 zc2 zc3 zc4 : Nat}
    (ez0 : z0 + 2 ^ 32 * zc1 = a2 * (5 * q2) + 0 + y0) (ez1 : z1 + 2 ^ 32 * zc2 = a3 * (5 * q2) + zc1 + y1)
    (ez2 : z2 + 2 ^ 32 * zc3 = a0 * (4 * q2) + zc2 + y2) (ez3 : z3 + 2 ^ 32 * zc4 = a1 * (4 * q2) + zc3 + y3)
    (ez4 : z4 = (y4 + zc4) % 2 ^ 32)
    {w0 w1 w2 w3 w4 wc1 wc2 wc3 wc4 : Nat}
    (ew0 : w0 + 2 ^ 32 * wc1 = a1 * (5 * q3) + 0 + z0) (ew1 : w1 + 2 ^ 32 * wc2 = a2 * (5 * q3) + wc1 + z1)
    (ew2 : w2 + 2 ^ 32 * wc3 = a3 * (5 * q3) + wc2 + z2) (ew3 : w3 + 2 ^ 32 * wc4 = a0 * (4 * q3) + wc3 + z3)
    (ew4 : w4 = (z4 + wc4) % 2 ^ 32) :
    val5 w0 w1 w2 w3 w4 % P = (val5 a0 a1 a2 a3 a4 * key r0 q1 q2 q3) % P ∧ w4 < topMax := by
  -- The bounds of the products.
  have b0 := prod_le (Nat.le_of_lt_succ (show a0 < 2 ^ 32 - 1 + 1 from ha0)) (Nat.le_of_lt_succ (show r0 < 2 ^ 28 - 1 + 1 from hr0))
  have b1 := prod_le (Nat.le_of_lt_succ (show a1 < 2 ^ 32 - 1 + 1 from ha1)) (Nat.le_of_lt_succ (show r0 < 2 ^ 28 - 1 + 1 from hr0))
  have b2 := prod_le (Nat.le_of_lt_succ (show a2 < 2 ^ 32 - 1 + 1 from ha2)) (Nat.le_of_lt_succ (show r0 < 2 ^ 28 - 1 + 1 from hr0))
  have b3 := prod_le (Nat.le_of_lt_succ (show a3 < 2 ^ 32 - 1 + 1 from ha3)) (Nat.le_of_lt_succ (show r0 < 2 ^ 28 - 1 + 1 from hr0))
  have b4 := prod_le ha4 (Nat.le_of_lt_succ (show r0 < 2 ^ 28 - 1 + 1 from hr0))
  have s41 := prod_le ha4 (show 5 * q1 ≤ 5 * (2 ^ 26 - 1) by omega_using [hq1])
  have s42 := prod_le ha4 (show 5 * q2 ≤ 5 * (2 ^ 26 - 1) by omega_using [hq2])
  have s43 := prod_le ha4 (show 5 * q3 ≤ 5 * (2 ^ 26 - 1) by omega_using [hq3])
  have s31 := prod_le (Nat.le_of_lt_succ (show a3 < 2 ^ 32 - 1 + 1 from ha3)) (show 5 * q1 ≤ 5 * (2 ^ 26 - 1) by omega_using [hq1])
  have r01 := prod_le (Nat.le_of_lt_succ (show a0 < 2 ^ 32 - 1 + 1 from ha0)) (show 4 * q1 ≤ 4 * (2 ^ 26 - 1) by omega_using [hq1])
  have r11 := prod_le (Nat.le_of_lt_succ (show a1 < 2 ^ 32 - 1 + 1 from ha1)) (show 4 * q1 ≤ 4 * (2 ^ 26 - 1) by omega_using [hq1])
  have r21 := prod_le (Nat.le_of_lt_succ (show a2 < 2 ^ 32 - 1 + 1 from ha2)) (show 4 * q1 ≤ 4 * (2 ^ 26 - 1) by omega_using [hq1])
  have s22 := prod_le (Nat.le_of_lt_succ (show a2 < 2 ^ 32 - 1 + 1 from ha2)) (show 5 * q2 ≤ 5 * (2 ^ 26 - 1) by omega_using [hq2])
  have s32 := prod_le (Nat.le_of_lt_succ (show a3 < 2 ^ 32 - 1 + 1 from ha3)) (show 5 * q2 ≤ 5 * (2 ^ 26 - 1) by omega_using [hq2])
  have r02 := prod_le (Nat.le_of_lt_succ (show a0 < 2 ^ 32 - 1 + 1 from ha0)) (show 4 * q2 ≤ 4 * (2 ^ 26 - 1) by omega_using [hq2])
  have r12 := prod_le (Nat.le_of_lt_succ (show a1 < 2 ^ 32 - 1 + 1 from ha1)) (show 4 * q2 ≤ 4 * (2 ^ 26 - 1) by omega_using [hq2])
  have s13 := prod_le (Nat.le_of_lt_succ (show a1 < 2 ^ 32 - 1 + 1 from ha1)) (show 5 * q3 ≤ 5 * (2 ^ 26 - 1) by omega_using [hq3])
  have s23 := prod_le (Nat.le_of_lt_succ (show a2 < 2 ^ 32 - 1 + 1 from ha2)) (show 5 * q3 ≤ 5 * (2 ^ 26 - 1) by omega_using [hq3])
  have s33 := prod_le (Nat.le_of_lt_succ (show a3 < 2 ^ 32 - 1 + 1 from ha3)) (show 5 * q3 ≤ 5 * (2 ^ 26 - 1) by omega_using [hq3])
  have r03 := prod_le (Nat.le_of_lt_succ (show a0 < 2 ^ 32 - 1 + 1 from ha0)) (show 4 * q3 ≤ 4 * (2 ^ 26 - 1) by omega_using [hq3])
  -- The number after each chain.
  have hx := first_arith ex0 ex1 ex2 ex3 ex4 (by omega_using [b0, b1, b2, b3, b4, s41, s42, s43])
  have hy := chain_arith ey0 ey1 ey2 ey3 ey4 (by rw [hx]; omega_using [b0, b1, b2, b3, b4, s41, s42, s43, s31, r01, r11, r21])
  have hz := chain_arith ez0 ez1 ez2 ez3 ez4 (by
    rw [hy, hx]; omega_using [b0, b1, b2, b3, b4, s41, s42, s43, s31, r01, r11, r21, s22, s32, r02, r12])
  have hw := chain_arith ew0 ew1 ew2 ew3 ew4 (by
    rw [hz, hy, hx]
    omega_using [b0, b1, b2, b3, b4, s41, s42, s43, s31, r01, r11, r21, s22, s32, r02, r12, s13, s23, s33, r03])
  rw [hz, hy, hx] at hw
  refine ⟨?_, ?_⟩
  · rw [expand, Nat.add_mul_mod_self_left, hw]
    congr 1
    omega_arith
  · simp only [val5] at hw
    show w4 < 3 * 2 ^ 30
    omega_using [hw, b0, b1, b2, b3, b4, s41, s42, s43, s31, r01, r11, r21, s22, s32, r02, r12, s13, s23, s33, r03]

/-! ## The final reduction -/

/-- The top word folded once more into `x` (a chain of the low words from
the carry `5 ⌊h4 / 4⌋`), the carry `e4` of `x + 5` out of the low words, and
`5 ⌊(x4 + e4) / 4⌋` added (a chain from that carry): `h mod p`, in five
words whose top one keeps two bits. -/
theorem reduce_arith {h0 h1 h2 h3 h4 x0 x1 x2 x3 c1 c2 c3 c4 y0 y1 y2 y3 e1 e2 e3 e4 w0 w1 w2 w3 k1 k2 k3 k4 : Nat}
    (hh0 : h0 < 2 ^ 32) (hh1 : h1 < 2 ^ 32) (hh2 : h2 < 2 ^ 32) (hh3 : h3 < 2 ^ 32)
    (hc : 5 * (h4 / 4) < 2 ^ 32)
    (hx0 : x0 < 2 ^ 32) (hx1 : x1 < 2 ^ 32) (hx2 : x2 < 2 ^ 32) (hx3 : x3 < 2 ^ 32)
    (hy0 : y0 < 2 ^ 32) (hy1 : y1 < 2 ^ 32) (hy2 : y2 < 2 ^ 32) (hy3 : y3 < 2 ^ 32)
    (hw0 : w0 < 2 ^ 32) (hw1 : w1 < 2 ^ 32) (hw2 : w2 < 2 ^ 32) (hw3 : w3 < 2 ^ 32)
    (ex0 : x0 + 2 ^ 32 * c1 = 5 * (h4 / 4) + h0) (ex1 : x1 + 2 ^ 32 * c2 = c1 + h1)
    (ex2 : x2 + 2 ^ 32 * c3 = c2 + h2) (ex3 : x3 + 2 ^ 32 * c4 = c3 + h3)
    (ey0 : y0 + 2 ^ 32 * e1 = 5 + x0) (ey1 : y1 + 2 ^ 32 * e2 = e1 + x1)
    (ey2 : y2 + 2 ^ 32 * e3 = e2 + x2) (ey3 : y3 + 2 ^ 32 * e4 = e3 + x3)
    (ew0 : w0 + 2 ^ 32 * k1 = 5 * ((e4 + (h4 % 4 + c4)) / 4) + x0) (ew1 : w1 + 2 ^ 32 * k2 = k1 + x1)
    (ew2 : w2 + 2 ^ 32 * k3 = k2 + x2) (ew3 : w3 + 2 ^ 32 * k4 = k3 + x3) :
    val5 w0 w1 w2 w3 ((h4 % 4 + c4 + k4) % 4) = val5 h0 h1 h2 h3 h4 % P := by
  -- The numbers of the three chains, by their low four words.
  obtain hX : x0 + 2 ^ 32 * x1 + 2 ^ 64 * x2 + 2 ^ 96 * x3 + 2 ^ 128 * c4 =
      5 * (h4 / 4) + (h0 + 2 ^ 32 * h1 + 2 ^ 64 * h2 + 2 ^ 96 * h3) := by omega_using [ex0, ex1, ex2, ex3]
  obtain hY : y0 + 2 ^ 32 * y1 + 2 ^ 64 * y2 + 2 ^ 96 * y3 + 2 ^ 128 * e4 =
      5 + (x0 + 2 ^ 32 * x1 + 2 ^ 64 * x2 + 2 ^ 96 * x3) := by omega_using [ey0, ey1, ey2, ey3]
  obtain hW : w0 + 2 ^ 32 * w1 + 2 ^ 64 * w2 + 2 ^ 96 * w3 + 2 ^ 128 * k4 =
      5 * ((e4 + (h4 % 4 + c4)) / 4) + (x0 + 2 ^ 32 * x1 + 2 ^ 64 * x2 + 2 ^ 96 * x3) := by
    omega_using [ew0, ew1, ew2, ew3]
  obtain bh : h0 + 2 ^ 32 * h1 + 2 ^ 64 * h2 + 2 ^ 96 * h3 < 2 ^ 128 := by omega_using [hh0, hh1, hh2, hh3]
  obtain bx : x0 + 2 ^ 32 * x1 + 2 ^ 64 * x2 + 2 ^ 96 * x3 < 2 ^ 128 := by omega_using [hx0, hx1, hx2, hx3]
  obtain by' : y0 + 2 ^ 32 * y1 + 2 ^ 64 * y2 + 2 ^ 96 * y3 < 2 ^ 128 := by omega_using [hy0, hy1, hy2, hy3]
  obtain bw : w0 + 2 ^ 32 * w1 + 2 ^ 64 * w2 + 2 ^ 96 * w3 < 2 ^ 128 := by omega_using [hw0, hw1, hw2, hw3]
  simp only [val5]
  generalize h0 + 2 ^ 32 * h1 + 2 ^ 64 * h2 + 2 ^ 96 * h3 = hl at hX bh ⊢
  generalize x0 + 2 ^ 32 * x1 + 2 ^ 64 * x2 + 2 ^ 96 * x3 = xl at hX hY hW bx
  generalize y0 + 2 ^ 32 * y1 + 2 ^ 64 * y2 + 2 ^ 96 * y3 = yl at hY by'
  generalize w0 + 2 ^ 32 * w1 + 2 ^ 64 * w2 + 2 ^ 96 * w3 = wl at hW bw ⊢
  -- The carries, and the multiple of `p` taken off.
  obtain hc4 : c4 ≤ 1 := by omega_using [hX, bh, bx, hc]
  obtain he4 : e4 ≤ 1 := by omega_using [hY, bx, by']
  generalize hq : h4 / 4 = q at hX hc
  generalize ht : h4 % 4 = t at hW ⊢
  obtain eh : h4 = 4 * q + t := by omega_using [hq, ht]
  obtain bt : t < 4 := by omega_using [ht]
  generalize hcc : (e4 + (t + c4)) / 4 = cc at hW
  obtain bcc : cc ≤ 1 := by omega_using [hcc, he4, hc4, bt]
  obtain ⟨hlt, heq⟩ : wl + 2 ^ 128 * ((t + c4 + k4) % 4) < P ∧
      hl + 2 ^ 128 * h4 = wl + 2 ^ 128 * ((t + c4 + k4) % 4) + P * (q + cc) := by
    simp only [P]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp bcc with hz | ho
    · -- `x + 5 < 2¹³⁰`: nothing is added, and `x < p`.
      obtain hk : k4 = 0 := by omega_using [hW, bx, bw, hz]
      obtain hs : e4 + (t + c4) < 4 := by omega_using [hcc, hz]
      rw [hk, Nat.add_zero, Nat.mod_eq_of_lt (by omega_using [hs])]
      omega_using [hX, hY, hW, bh, bx, by', bw, hs, eh, hk, hz]
    · -- `x + 5 ≥ 2¹³⁰`: the sum is `x + 5`, whose bit 130 is dropped.
      obtain hk : k4 = e4 := by omega_using [hY, hW, bx, by', bw, ho]
      obtain hs : 4 ≤ e4 + (t + c4) ∧ e4 + (t + c4) < 6 := by omega_using [hcc, ho, he4, hc4, bt]
      obtain hm : (t + c4 + k4) % 4 = t + c4 + k4 - 4 := by omega_using [hs, hk]
      rw [hm]
      omega_using [hX, hY, hW, bh, bx, by', bw, hs, eh, hk, ho]
  rw [heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-- A number of four words added to the low four words of another, in a
chain: the sum modulo `2¹²⁸`. -/
theorem sum_arith {w0 w1 w2 w3 w4 s0 s1 s2 s3 t0 t1 t2 t3 c1 c2 c3 c4 : Nat}
    (ht0 : t0 < 2 ^ 32) (ht1 : t1 < 2 ^ 32) (ht2 : t2 < 2 ^ 32) (ht3 : t3 < 2 ^ 32)
    (e0 : t0 + 2 ^ 32 * c1 = s0 + w0) (e1 : t1 + 2 ^ 32 * c2 = s1 + c1 + w1)
    (e2 : t2 + 2 ^ 32 * c3 = s2 + c2 + w2) (e3 : t3 + 2 ^ 32 * c4 = s3 + c3 + w3) :
    t0 + 2 ^ 32 * t1 + 2 ^ 64 * t2 + 2 ^ 96 * t3 =
      (val5 w0 w1 w2 w3 w4 + (s0 + 2 ^ 32 * s1 + 2 ^ 64 * s2 + 2 ^ 96 * s3)) % 2 ^ 128 := by
  simp only [val5]
  omega_using [ht0, ht1, ht2, ht3, e0, e1, e2, e3]

end VG.Proof.Poly1305.Limbs32
