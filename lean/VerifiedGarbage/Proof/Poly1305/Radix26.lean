module

public import VerifiedGarbage.Spec.Poly1305
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# Poly1305: the arithmetic in radix `2²⁶`

The numbers the radix-`2²⁶` implementations compute
(`Impl/Poly1305/AArch64.lean`, `Impl/Poly1305/PPC64LE.lean`), as natural
numbers: five limbs `a0, …, a4` stand for `val5 a0 a1 a2 a3 a4 = a0 + 2²⁶ a1 +
2⁵² a2 + 2⁷⁸ a3 + 2¹⁰⁴ a4`.
-/

@[expose] public section

namespace VG.Proof.Poly1305.Radix26

open VG.Spec.Poly1305 (P)

/-- The number with the limbs `a0, …, a4`. -/
def val5 (a0 a1 a2 a3 a4 : Nat) : Nat := a0 + 2 ^ 26 * a1 + 2 ^ 52 * a2 + 2 ^ 78 * a3 + 2 ^ 104 * a4

/-- Limb `j` of `N`: 26 bits, but for the last, which has the rest. -/
def lim (N j : Nat) : Nat := if j < 4 then N / 2 ^ (26 * j) % 2 ^ 26 else N / 2 ^ 104

theorem lim0 (N : Nat) : lim N 0 = N % 2 ^ 26 := by simp only [lim, Nat.zero_lt_succ, ↓reduceIte, Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.reducePow]
theorem lim1 (N : Nat) : lim N 1 = N / 2 ^ 26 % 2 ^ 26 := by simp only [lim, Nat.reduceLT, ↓reduceIte, Nat.mul_one, Nat.reducePow]
theorem lim2 (N : Nat) : lim N 2 = N / 2 ^ 52 % 2 ^ 26 := by simp only [lim, Nat.reduceLT, ↓reduceIte, Nat.reduceMul, Nat.reducePow]
theorem lim3 (N : Nat) : lim N 3 = N / 2 ^ 78 % 2 ^ 26 := by simp only [lim, Nat.lt_add_one, ↓reduceIte, Nat.reduceMul, Nat.reducePow]
theorem lim4 (N : Nat) : lim N 4 = N / 2 ^ 104 := by simp only [lim, Nat.lt_irrefl, ↓reduceIte, Nat.reducePow]

theorem val5_lim (N : Nat) : val5 (lim N 0) (lim N 1) (lim N 2) (lim N 3) (lim N 4) = N := by
  simp only [val5, lim0, lim1, lim2, lim3, lim4]
  omega_using []

theorem lim_lt (N : Nat) {j : Nat} (hj : j < 4) : lim N j < 2 ^ 26 := by
  simp only [lim, hj, ite_true]
  exact Nat.mod_lt _ (by decide)

theorem lim4_lt {N : Nat} (h : N < 2 ^ 128) : lim N 4 < 2 ^ 24 := by
  rw [lim4]; omega_using [h]

/-- The limbs `split` computes from the words `lo, hi`. -/
theorem split_arith (lo hi : Nat) (hlo : lo < 2 ^ 64) :
    lo % 2 ^ 26 = lim (lo + 2 ^ 64 * hi) 0 ∧
    lo / 2 ^ 26 % 2 ^ 26 = lim (lo + 2 ^ 64 * hi) 1 ∧
    (lo / 2 ^ 52 + hi * 2 ^ 12 % 2 ^ 64) % 2 ^ 64 % 2 ^ 26 = lim (lo + 2 ^ 64 * hi) 2 ∧
    hi / 2 ^ 14 % 2 ^ 26 = lim (lo + 2 ^ 64 * hi) 3 ∧
    hi / 2 ^ 40 = lim (lo + 2 ^ 64 * hi) 4 := by
  simp only [lim0, lim1, lim2, lim3, lim4]
  refine ⟨by omega_using [], by omega_using [], by omega_using [], by omega_using [hlo], by omega_using [hlo]⟩

/-! ## Absorbing a block -/

/-- The sums of products `dk` of the limbs `a` and `r` (with `sj = 5 rj`). -/
theorem product_identity (a0 a1 a2 a3 a4 r0 r1 r2 r3 r4 : Nat) :
    val5 a0 a1 a2 a3 a4 * val5 r0 r1 r2 r3 r4 =
      val5 (a0 * r0 + a1 * (5 * r4) + a2 * (5 * r3) + a3 * (5 * r2) + a4 * (5 * r1))
        (a0 * r1 + a1 * r0 + a2 * (5 * r4) + a3 * (5 * r3) + a4 * (5 * r2))
        (a0 * r2 + a1 * r1 + a2 * r0 + a3 * (5 * r4) + a4 * (5 * r3))
        (a0 * r3 + a1 * r2 + a2 * r1 + a3 * r0 + a4 * (5 * r4))
        (a0 * r4 + a1 * r3 + a2 * r2 + a3 * r1 + a4 * r0) +
      P * (a1 * r4 + a2 * r3 + a3 * r2 + a4 * r1 + 2 ^ 26 * (a2 * r4 + a3 * r3 + a4 * r2) +
        2 ^ 52 * (a3 * r4 + a4 * r3) + 2 ^ 78 * (a4 * r4)) := by
  have hP : P + 5 = 2 ^ 130 := by simp only [P, Nat.reducePow, Nat.reduceSub, Nat.reduceAdd]
  have e : val5 a0 a1 a2 a3 a4 * val5 r0 r1 r2 r3 r4 +
      5 * (a1 * r4 + a2 * r3 + a3 * r2 + a4 * r1 + 2 ^ 26 * (a2 * r4 + a3 * r3 + a4 * r2) +
        2 ^ 52 * (a3 * r4 + a4 * r3) + 2 ^ 78 * (a4 * r4)) =
      val5 (a0 * r0 + a1 * (5 * r4) + a2 * (5 * r3) + a3 * (5 * r2) + a4 * (5 * r1))
        (a0 * r1 + a1 * r0 + a2 * (5 * r4) + a3 * (5 * r3) + a4 * (5 * r2))
        (a0 * r2 + a1 * r1 + a2 * r0 + a3 * (5 * r4) + a4 * (5 * r3))
        (a0 * r3 + a1 * r2 + a2 * r1 + a3 * r0 + a4 * (5 * r4))
        (a0 * r4 + a1 * r3 + a2 * r2 + a3 * r1 + a4 * r0) +
      2 ^ 130 * (a1 * r4 + a2 * r3 + a3 * r2 + a4 * r1 + 2 ^ 26 * (a2 * r4 + a3 * r3 + a4 * r2) +
        2 ^ 52 * (a3 * r4 + a4 * r3) + 2 ^ 78 * (a4 * r4)) := by
    simp only [val5]; grind
  rw [← hP, Nat.add_mul, ← Nat.add_assoc] at e
  exact Nat.add_right_cancel e

theorem mul_lt' {a b c d : Nat} (h₁ : a < c) (h₂ : b < d) : a * b < c * d :=
  Nat.mul_lt_mul_of_lt_of_lt h₁ h₂

/-- The sums of products `products` computes (as `dform` states them), from
the limbs `a` of `h + m` and those of the clamped `R`: they fit in 60 bits,
and they are the limbs of a number congruent to `(h + m) R`. -/
theorem dsum_arith {a0 a1 a2 a3 a4 R : Nat} (ha0 : a0 < 2 ^ 28) (ha1 : a1 < 2 ^ 28)
    (ha2 : a2 < 2 ^ 28) (ha3 : a3 < 2 ^ 28) (ha4 : a4 < 2 ^ 28) (hR : R < 2 ^ 128) :
    let d0 := a0 * lim R 0 + (a1 * (5 * lim R 4) + (a2 * (5 * lim R 3) + (a3 * (5 * lim R 2) +
      (a4 * (5 * lim R 1) + 0))))
    let d1 := a0 * lim R 1 + (a1 * lim R 0 + (a2 * (5 * lim R 4) + (a3 * (5 * lim R 3) +
      (a4 * (5 * lim R 2) + 0))))
    let d2 := a0 * lim R 2 + (a1 * lim R 1 + (a2 * lim R 0 + (a3 * (5 * lim R 4) +
      (a4 * (5 * lim R 3) + 0))))
    let d3 := a0 * lim R 3 + (a1 * lim R 2 + (a2 * lim R 1 + (a3 * lim R 0 + (a4 * (5 * lim R 4) + 0))))
    let d4 := a0 * lim R 4 + (a1 * lim R 3 + (a2 * lim R 2 + (a3 * lim R 1 + (a4 * lim R 0 + 0))))
    d0 < 2 ^ 60 ∧ d1 < 2 ^ 60 ∧ d2 < 2 ^ 60 ∧ d3 < 2 ^ 60 ∧ d4 < 2 ^ 60 ∧
      val5 d0 d1 d2 d3 d4 % P = (val5 a0 a1 a2 a3 a4 * R) % P := by
  intro d0 d1 d2 d3 d4
  have r0 := lim_lt R (j := 0) (by decide); have r1 := lim_lt R (j := 1) (by decide)
  have r2 := lim_lt R (j := 2) (by decide); have r3 := lim_lt R (j := 3) (by decide)
  have r4 := Nat.lt_trans (lim4_lt hR) (show 2 ^ 24 < 2 ^ 26 by decide)
  have e := product_identity a0 a1 a2 a3 a4 (lim R 0) (lim R 1) (lim R 2) (lim R 3) (lim R 4)
  rw [val5_lim] at e
  -- Every product is less than `2⁵⁷`.
  have p : ∀ a j, a < 2 ^ 28 → j < 2 ^ 26 → a * j < 2 ^ 57 ∧ a * (5 * j) < 2 ^ 57 := by
    intro a j ha hj
    have h1 := mul_lt' ha hj
    have h2 := mul_lt' ha (show 5 * j < 5 * 2 ^ 26 by omega_using [hj])
    exact ⟨by omega_using [h1], by omega_using [h2]⟩
  obtain ⟨p00, p00'⟩ := p a0 _ ha0 r0; obtain ⟨p01, p01'⟩ := p a0 _ ha0 r1
  obtain ⟨p02, p02'⟩ := p a0 _ ha0 r2; obtain ⟨p03, p03'⟩ := p a0 _ ha0 r3
  obtain ⟨p04, p04'⟩ := p a0 _ ha0 r4
  obtain ⟨p10, p10'⟩ := p a1 _ ha1 r0; obtain ⟨p11, p11'⟩ := p a1 _ ha1 r1
  obtain ⟨p12, p12'⟩ := p a1 _ ha1 r2; obtain ⟨p13, p13'⟩ := p a1 _ ha1 r3
  obtain ⟨p14, p14'⟩ := p a1 _ ha1 r4
  obtain ⟨p20, p20'⟩ := p a2 _ ha2 r0; obtain ⟨p21, p21'⟩ := p a2 _ ha2 r1
  obtain ⟨p22, p22'⟩ := p a2 _ ha2 r2; obtain ⟨p23, p23'⟩ := p a2 _ ha2 r3
  obtain ⟨p24, p24'⟩ := p a2 _ ha2 r4
  obtain ⟨p30, p30'⟩ := p a3 _ ha3 r0; obtain ⟨p31, p31'⟩ := p a3 _ ha3 r1
  obtain ⟨p32, p32'⟩ := p a3 _ ha3 r2; obtain ⟨p33, p33'⟩ := p a3 _ ha3 r3
  obtain ⟨p34, p34'⟩ := p a3 _ ha3 r4
  obtain ⟨p40, p40'⟩ := p a4 _ ha4 r0; obtain ⟨p41, p41'⟩ := p a4 _ ha4 r1
  obtain ⟨p42, p42'⟩ := p a4 _ ha4 r2; obtain ⟨p43, p43'⟩ := p a4 _ ha4 r3
  obtain ⟨p44, p44'⟩ := p a4 _ ha4 r4
  refine ⟨by omega_using [p00, p14', p23', p32', p41'], by omega_using [p01, p10, p24', p33', p42'],
    by omega_using [p02, p11, p20, p34', p43'], by omega_using [p03, p12, p21, p30, p44'],
    by omega_using [p04, p13, p22, p31, p40], ?_⟩
  rw [e, Nat.add_mul_mod_self_left]
  have : val5 d0 d1 d2 d3 d4 =
      val5 (a0 * lim R 0 + a1 * (5 * lim R 4) + a2 * (5 * lim R 3) + a3 * (5 * lim R 2) +
          a4 * (5 * lim R 1))
        (a0 * lim R 1 + a1 * lim R 0 + a2 * (5 * lim R 4) + a3 * (5 * lim R 3) + a4 * (5 * lim R 2))
        (a0 * lim R 2 + a1 * lim R 1 + a2 * lim R 0 + a3 * (5 * lim R 4) + a4 * (5 * lim R 3))
        (a0 * lim R 3 + a1 * lim R 2 + a2 * lim R 1 + a3 * lim R 0 + a4 * (5 * lim R 4))
        (a0 * lim R 4 + a1 * lim R 3 + a2 * lim R 2 + a3 * lim R 1 + a4 * lim R 0) := by
    simp only [d0, d1, d2, d3, d4, Nat.add_zero, Nat.add_assoc]
  rw [this]

theorem val5_lt {a0 a1 a2 a3 a4 : Nat} (b0 : a0 < 2 ^ 26) (b1 : a1 < 2 ^ 26) (b2 : a2 < 2 ^ 26)
    (b3 : a3 < 2 ^ 26) (b4 : a4 < 2 ^ 26) : val5 a0 a1 a2 a3 a4 < 2 ^ 130 := by
  simp only [val5]; omega_using [b0, b1, b2, b3, b4]

theorem val5_le {a0 a1 a2 a3 a4 : Nat} (b0 : a0 < 2 ^ 26) (b1 : a1 < 2 ^ 26) (b2 : a2 < 2 ^ 26)
    (b3 : a3 < 2 ^ 26) (b4 : a4 ≤ 2 ^ 26) : val5 a0 a1 a2 a3 a4 < 2 ^ 130 + 2 ^ 104 := by
  simp only [val5]; omega_using [b0, b1, b2, b3, b4]

theorem dm26 {x c e : Nat} (hc : c = x / 2 ^ 26) (he : e = x % 2 ^ 26) :
    x = 2 ^ 26 * c + e ∧ e < 2 ^ 26 := by
  subst hc he; exact ⟨(Nat.div_add_mod x _).symm, Nat.mod_lt _ (by decide)⟩

theorem mod64 {x y : Nat} (h : x = y % 2 ^ 64) (hy : y < 2 ^ 64) : x = y :=
  h.trans (Nat.mod_eq_of_lt hy)

/-- The carries of `absorb` (as `carry` computes them): from the sums of
products `d0, …, d4` to the new limbs, `2¹³⁰ ≡ 5` folding the carry `c4` out
of `d4` into the bottom. -/
theorem carry_arith {d0 d1 d2 d3 d4 c0 e0 d1' c1 e1 d2' c2 e2 d3' c2' e3 d4' c4 e4 q c5 f c6 f0 g1 : Nat}
    (h0 : d0 < 2 ^ 60) (h1 : d1 < 2 ^ 60) (h2 : d2 < 2 ^ 60) (h3 : d3 < 2 ^ 60) (h4 : d4 < 2 ^ 60)
    (q0 : c0 = d0 / 2 ^ 26) (q1 : e0 = d0 % 2 ^ 26) (q2 : d1' = (d1 + c0) % 2 ^ 64)
    (q3 : c1 = d1' / 2 ^ 26) (q4 : e1 = d1' % 2 ^ 26) (q5 : d2' = (d2 + c1) % 2 ^ 64)
    (q6 : c2 = d2' / 2 ^ 26) (q7 : e2 = d2' % 2 ^ 26) (q8 : d3' = (d3 + c2) % 2 ^ 64)
    (q9 : c2' = d3' / 2 ^ 26) (q10 : e3 = d3' % 2 ^ 26) (q11 : d4' = (d4 + c2') % 2 ^ 64)
    (q12 : c4 = d4' / 2 ^ 26) (q13 : e4 = d4' % 2 ^ 26) (q14 : q = c4 * 2 ^ 2 % 2 ^ 64)
    (q15 : c5 = (c4 + q) % 2 ^ 64) (q16 : f = (e0 + c5) % 2 ^ 64)
    (q17 : c6 = f / 2 ^ 26) (q18 : f0 = f % 2 ^ 26) (q19 : g1 = (e1 + c6) % 2 ^ 64) :
    val5 f0 g1 e2 e3 e4 + P * c4 = val5 d0 d1 d2 d3 d4 ∧
      f0 < 2 ^ 26 ∧ g1 < 2 ^ 27 ∧ e2 < 2 ^ 26 ∧ e3 < 2 ^ 26 ∧ e4 < 2 ^ 26 := by
  obtain ⟨l0, b0⟩ := dm26 q0 q1
  have C0 : c0 < 2 ^ 34 := by omega_using [h0, l0]
  have r2 := mod64 q2 (by omega_using [h1, C0])
  obtain ⟨l1, b1⟩ := dm26 q3 q4
  have C1 : c1 < 2 ^ 35 := by omega_using [h1, C0, r2, l1]
  have r5 := mod64 q5 (by omega_using [h2, C1])
  obtain ⟨l2, b2⟩ := dm26 q6 q7
  have C2 : c2 < 2 ^ 35 := by omega_using [h2, C1, r5, l2]
  have r8 := mod64 q8 (by omega_using [h3, C2])
  obtain ⟨l3, b3⟩ := dm26 q9 q10
  have C3 : c2' < 2 ^ 35 := by omega_using [h3, C2, r8, l3]
  have r11 := mod64 q11 (by omega_using [h4, C3])
  obtain ⟨l4, b4⟩ := dm26 q12 q13
  have c4b : c4 < 2 ^ 35 := by omega_using [h4, C3, r11, l4]
  have r14 := mod64 q14 (by omega_using [c4b])
  have r15 := mod64 q15 (by omega_using [c4b, r14])
  have r16 := mod64 q16 (by omega_using [c4b, b0, r14, r15])
  obtain ⟨l6, b6⟩ := dm26 q17 q18
  have r19 := mod64 q19 (by omega_using [c4b, b0, b1, r14, r15, r16, l6])
  simp only [val5, P]
  refine ⟨?_, b6, ?_, b2, b3, b4⟩
  · omega_using [l0, r2, l1, r5, l2, r8, l3, r11, l4, r14, r15, r16, l6, r19]
  · omega_using [c4b, b0, b1, r14, r15, r16, l6, r19]

/-! ## The final reduction -/

/-- `normalize` and `plus5`: the limbs `h1, h2, h3` normalized (carrying into
`t4`), `g = h + 5` with carries, whose carry out `b` is 1 iff `g ≥ 2¹³⁰`:
then `g - 2¹³⁰` (the limbs `g0, …, g4`) is `h mod p`, and otherwise `h` is. -/
theorem reduce_arith {h0 h1 h2 h3 h4 n1 t2 n2 t3 n3 t4 u0 g0 u1 g1 u2 g2 u3 g3 u4 g4 b : Nat}
    (b0 : h0 < 2 ^ 26) (b1 : h1 < 2 ^ 27) (b2 : h2 < 2 ^ 26) (b3 : h3 < 2 ^ 26) (b4 : h4 < 2 ^ 26)
    (e1 : n1 = h1 % 2 ^ 26) (e2 : t2 = (h2 + h1 / 2 ^ 26) % 2 ^ 64)
    (e3 : n2 = t2 % 2 ^ 26) (e4 : t3 = (h3 + t2 / 2 ^ 26) % 2 ^ 64)
    (e5 : n3 = t3 % 2 ^ 26) (e6 : t4 = (h4 + t3 / 2 ^ 26) % 2 ^ 64)
    (f0 : u0 = (h0 + 5) % 2 ^ 64) (f1 : g0 = u0 % 2 ^ 26) (f2 : u1 = (n1 + u0 / 2 ^ 26) % 2 ^ 64)
    (f3 : g1 = u1 % 2 ^ 26) (f4 : u2 = (n2 + u1 / 2 ^ 26) % 2 ^ 64)
    (f5 : g2 = u2 % 2 ^ 26) (f6 : u3 = (n3 + u2 / 2 ^ 26) % 2 ^ 64)
    (f7 : g3 = u3 % 2 ^ 26) (f8 : u4 = (t4 + u3 / 2 ^ 26) % 2 ^ 64)
    (f9 : g4 = u4 % 2 ^ 26) (f10 : b = u4 / 2 ^ 26) :
    (b = 1 ∧ val5 g0 g1 g2 g3 g4 = val5 h0 h1 h2 h3 h4 % P ∧
        g0 < 2 ^ 26 ∧ g1 < 2 ^ 26 ∧ g2 < 2 ^ 26 ∧ g3 < 2 ^ 26 ∧ g4 < 2 ^ 26) ∨
      (b = 0 ∧ val5 h0 n1 n2 n3 t4 = val5 h0 h1 h2 h3 h4 % P ∧
        h0 < 2 ^ 26 ∧ n1 < 2 ^ 26 ∧ n2 < 2 ^ 26 ∧ n3 < 2 ^ 26 ∧ t4 < 2 ^ 26) := by
  have hP : P = 2 ^ 130 - 5 := rfl
  obtain ⟨k1, m1⟩ := dm26 (x := h1) rfl e1
  generalize h1 / 2 ^ 26 = a1 at k1 e2
  have A1 : a1 < 2 := by omega_using [b1, k1]
  have ht2 := mod64 e2 (by omega_using [b2, A1])
  obtain ⟨k2, m2⟩ := dm26 (x := t2) rfl e3
  generalize t2 / 2 ^ 26 = a2 at k2 e4
  have A2 : a2 < 2 := by omega_using [b2, A1, ht2, k2]
  have ht3 := mod64 e4 (by omega_using [b3, A2])
  obtain ⟨k3, m3⟩ := dm26 (x := t3) rfl e5
  generalize t3 / 2 ^ 26 = a3 at k3 e6
  have A3 : a3 < 2 := by omega_using [b3, A2, ht3, k3]
  have ht4 := mod64 e6 (by omega_using [b4, A3])
  have hn : n1 < 2 ^ 26 ∧ n2 < 2 ^ 26 ∧ n3 < 2 ^ 26 ∧ t4 ≤ 2 ^ 26 :=
    ⟨m1, m2, m3, by omega_using [b4, A3, ht4]⟩
  have hu0 := mod64 f0 (by omega_using [b0])
  obtain ⟨k4, m4⟩ := dm26 (x := u0) rfl f1
  generalize u0 / 2 ^ 26 = a4 at k4 f2
  have A4 : a4 < 2 := by omega_using [b0, hu0, k4]
  have hu1 := mod64 f2 (by omega_using [m1, A4])
  obtain ⟨k5, m5⟩ := dm26 (x := u1) rfl f3
  generalize u1 / 2 ^ 26 = a5 at k5 f4
  have A5 : a5 < 2 := by omega_using [m1, A4, hu1, k5]
  have hu2 := mod64 f4 (by omega_using [m2, A5])
  obtain ⟨k6, m6⟩ := dm26 (x := u2) rfl f5
  generalize u2 / 2 ^ 26 = a6 at k6 f6
  have A6 : a6 < 2 := by omega_using [m2, A5, hu2, k6]
  have hu3 := mod64 f6 (by omega_using [m3, A6])
  obtain ⟨k7, m7⟩ := dm26 (x := u3) rfl f7
  generalize u3 / 2 ^ 26 = a7 at k7 f8
  have A7 : a7 < 2 := by omega_using [m3, A6, hu3, k7]
  have hu4 := mod64 f8 (by omega_using [hn.2.2.2, A7])
  obtain ⟨k8, m8⟩ := dm26 f10 f9
  have hV : val5 h0 n1 n2 n3 t4 = val5 h0 h1 h2 h3 h4 := by
    simp only [val5]; omega_using [k1, ht2, k2, ht3, k3, ht4]
  have hG : val5 g0 g1 g2 g3 g4 + 2 ^ 130 * b = val5 h0 n1 n2 n3 t4 + 5 := by
    simp only [val5]; omega_using [k4, k5, k6, k7, k8, hu0, hu1, hu2, hu3, hu4]
  have hg : g0 < 2 ^ 26 ∧ g1 < 2 ^ 26 ∧ g2 < 2 ^ 26 ∧ g3 < 2 ^ 26 ∧ g4 < 2 ^ 26 :=
    ⟨m4, m5, m6, m7, m8⟩
  have hGl := val5_lt m4 m5 m6 m7 m8
  have hVl := val5_le b0 m1 m2 m3 hn.2.2.2
  rw [← hV]
  generalize val5 g0 g1 g2 g3 g4 = G at hG hGl ⊢
  generalize val5 h0 n1 n2 n3 t4 = V at hG hVl ⊢
  rcases (by omega_using [hn.2.2.2, A7, hu4, k8] : b = 0 ∨ b = 1) with h | h
  · right
    subst h
    have lt : V < P := by rw [hP]; omega_using [hG, hGl]
    exact ⟨rfl, (Nat.mod_eq_of_lt lt).symm, b0, hn.1, hn.2.1, hn.2.2.1, by omega_using [hu4, k8, m8]⟩
  · left
    subst h
    have e : V = G + P := by rw [hP]; omega_using [hG]
    have lt : G < P := by rw [hP]; omega_using [hG, hVl]
    refine ⟨rfl, ?_, hg⟩
    rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt lt]

/-- `pack`: normalized limbs (but for the last) as 64-bit words. -/
theorem pack_arith {l0 l1 l2 l3 l4 : Nat} (b0 : l0 < 2 ^ 26) (b1 : l1 < 2 ^ 26) (b2 : l2 < 2 ^ 26)
    (b3 : l3 < 2 ^ 26) :
    ((l0 + l1 * 2 ^ 26 % 2 ^ 64) % 2 ^ 64 + l2 * 2 ^ 52 % 2 ^ 64) % 2 ^ 64 =
        val5 l0 l1 l2 l3 l4 % 2 ^ 64 ∧
      ((l2 / 2 ^ 12 + l3 * 2 ^ 14 % 2 ^ 64) % 2 ^ 64 + l4 * 2 ^ 40 % 2 ^ 64) % 2 ^ 64 =
        val5 l0 l1 l2 l3 l4 / 2 ^ 64 % 2 ^ 64 ∧
      l4 / 2 ^ 24 = val5 l0 l1 l2 l3 l4 / 2 ^ 128 := by
  simp only [val5]
  refine ⟨by omega_using [], by omega_using [b0, b1], by omega_using [b0, b1, b2, b3]⟩

/-- Adding limbs `s0, …, s4` to limbs `h0, …, h4` (`addLimbs`), with the
carries propagated up to the last limb (`carryStep` and `normalize`). -/
theorem addCarry_arith {h0 h1 h2 h3 h4 s0 s1 s2 s3 s4 a0 a1 a2 a3 a4 b1 b2 b3 b4 : Nat}
    (hh0 : h0 < 2 ^ 27) (hh1 : h1 < 2 ^ 27) (hh2 : h2 < 2 ^ 27) (hh3 : h3 < 2 ^ 27)
    (hh4 : h4 < 2 ^ 27) (hs0 : s0 < 2 ^ 27) (hs1 : s1 < 2 ^ 27) (hs2 : s2 < 2 ^ 27)
    (hs3 : s3 < 2 ^ 27) (hs4 : s4 < 2 ^ 27)
    (e0 : a0 = (h0 + s0) % 2 ^ 64) (e1 : a1 = (h1 + s1) % 2 ^ 64) (e2 : a2 = (h2 + s2) % 2 ^ 64)
    (e3 : a3 = (h3 + s3) % 2 ^ 64) (e4 : a4 = (h4 + s4) % 2 ^ 64)
    (c1 : b1 = (a1 + a0 / 2 ^ 26) % 2 ^ 64) (c2 : b2 = (a2 + b1 / 2 ^ 26) % 2 ^ 64)
    (c3 : b3 = (a3 + b2 / 2 ^ 26) % 2 ^ 64) (c4 : b4 = (a4 + b3 / 2 ^ 26) % 2 ^ 64) :
    val5 (a0 % 2 ^ 26) (b1 % 2 ^ 26) (b2 % 2 ^ 26) (b3 % 2 ^ 26) b4 =
      val5 h0 h1 h2 h3 h4 + val5 s0 s1 s2 s3 s4 ∧ b4 < 2 ^ 29 := by
  have r0 := mod64 e0 (by omega_using [hh0, hs0])
  have r1 := mod64 e1 (by omega_using [hh1, hs1])
  have r2 := mod64 e2 (by omega_using [hh2, hs2])
  have r3 := mod64 e3 (by omega_using [hh3, hs3])
  have r4 := mod64 e4 (by omega_using [hh4, hs4])
  obtain ⟨k0, m0⟩ := dm26 (x := a0) rfl rfl
  generalize a0 / 2 ^ 26 = z0 at k0 c1
  generalize a0 % 2 ^ 26 = w0 at k0 m0 ⊢
  have Z0 : z0 < 8 := by omega_using [hh0, hs0, r0, k0]
  have q1 := mod64 c1 (by omega_using [hh1, hs1, r1, Z0])
  obtain ⟨k1, m1⟩ := dm26 (x := b1) rfl rfl
  generalize b1 / 2 ^ 26 = z1 at k1 c2
  generalize b1 % 2 ^ 26 = w1 at k1 m1 ⊢
  have Z1 : z1 < 8 := by omega_using [hh1, hs1, r1, Z0, q1, k1]
  have q2 := mod64 c2 (by omega_using [hh2, hs2, r2, Z1])
  obtain ⟨k2, m2⟩ := dm26 (x := b2) rfl rfl
  generalize b2 / 2 ^ 26 = z2 at k2 c3
  generalize b2 % 2 ^ 26 = w2 at k2 m2 ⊢
  have Z2 : z2 < 8 := by omega_using [hh2, hs2, r2, Z1, q2, k2]
  have q3 := mod64 c3 (by omega_using [hh3, hs3, r3, Z2])
  obtain ⟨k3, m3⟩ := dm26 (x := b3) rfl rfl
  generalize b3 / 2 ^ 26 = z3 at k3 c4
  generalize b3 % 2 ^ 26 = w3 at k3 m3 ⊢
  have Z3 : z3 < 8 := by omega_using [hh3, hs3, r3, Z2, q3, k3]
  have q4 := mod64 c4 (by omega_using [hh4, hs4, r4, Z3])
  refine ⟨?_, by omega_using [hh4, hs4, r4, Z3, q4]⟩
  simp only [val5]
  omega_using [r0, r1, r2, r3, r4, k0, q1, k1, q2, k2, q3, k3, q4]

end VG.Proof.Poly1305.Radix26
