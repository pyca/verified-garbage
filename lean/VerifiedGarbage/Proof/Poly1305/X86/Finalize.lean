import VerifiedGarbage.Spec.Poly1305
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Impl.Poly1305.X86
import VerifiedGarbage.Proof.Poly1305.X86.Lit
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Poly1305.Stream
import VerifiedGarbage.Proof.Framework.X86.Inline
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Poly1305.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.Poly1305.X86.Blocks`. -/
section

/-!
# Poly1305 on x86: carries and digits, for `omega` on small linear problems

`omega` handles `x / n` and `x % n` by introducing a new variable and its
constraints, in every call, and a chain of carries `(a + (b + c / n) / n) % m`
makes every call pay for all of them (and the kernel check a large
certificate). Name each carry once instead: `divMod` states
`x = n * (x / n) + x % n`, and after `generalize x / n = c` the later steps
are linear in `c`; `eq_of_mod` drops a `% m` that does not wrap; `digit`
reads a digit off a sum without `omega`.
-/

namespace VG.Carry

/-- `x` as a quotient and a remainder, to `generalize` both. -/
theorem divMod (x n : Nat) : x = n * (x / n) + x % n := (Nat.div_add_mod x n).symm

/-- `x = n * c + e`, with `e < n`, from `c = x / n` and `e = x % n`. -/
theorem of_divMod {x c e n : Nat} (hn : 0 < n) (hc : c = x / n) (he : e = x % n) :
    x = n * c + e ∧ e < n := by
  subst hc he; exact ⟨(Nat.div_add_mod x n).symm, Nat.mod_lt _ hn⟩

/-- A reduction modulo `m` that does not wrap. -/
theorem eq_of_mod {x y m : Nat} (h : x = y % m) (hy : y < m) : x = y :=
  h.trans (Nat.mod_eq_of_lt hy)

/-- The lowest digit of `u + n W` and the rest, for `u < n`. -/
theorem digit {u n : Nat} (W : Nat) (hu : u < n) : (u + n * W) % n = u ∧ (u + n * W) / n = W :=
  ⟨by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hu],
   by rw [Nat.add_mul_div_left _ _ (Nat.lt_of_le_of_lt (Nat.zero_le _) hu), Nat.div_eq_of_lt hu,
     Nat.zero_add]⟩

end VG.Carry

-- Formerly the module `VerifiedGarbage.Proof.Poly1305.X86.Steps`.
section

section

/-!
# Poly1305 on x86 (32-bit): the arithmetic in radix `2³²`

The numbers the code computes (see `Impl/Poly1305/X86.lean`), as natural
numbers: five words `a0, …, a4` stand for `val5 a0 a1 a2 a3 a4 = a0 + 2³² a1 +
2⁶⁴ a2 + 2⁹⁶ a3 + 2¹²⁸ a4`, and the clamped `r` for `r0 + 2³² 4 q1 + 2⁶⁴ 4 q2 +
2⁹⁶ 4 q3`, with `sj = 5 qj`. The products are named so that `omega` treats
them as atoms.
-/

namespace VG.Proof.Poly1305.X86

open VG.Spec.Poly1305 (P)

/-- The number with the words `a0, …, a4`. -/
def val5 (a0 a1 a2 a3 a4 : Nat) : Nat := a0 + 2 ^ 32 * a1 + 2 ^ 64 * a2 + 2 ^ 96 * a3 + 2 ^ 128 * a4

/-- The clamped `r`, from `r0` and `rj = 4 qj`. -/
def rval (r0 q1 q2 q3 : Nat) : Nat := r0 + 2 ^ 32 * (4 * q1) + 2 ^ 64 * (4 * q2) + 2 ^ 96 * (4 * q3)

/-- `(a0 + … + 2¹²⁸ a4) r`: the terms of weight `2¹²⁸` and up but `a4 r0` are
folded into the bottom as multiples of `5 qj`, leaving a multiple of `p`. -/
theorem fold_identity (a0 a1 a2 a3 a4 r0 q1 q2 q3 : Nat) :
    VG.Proof.Poly1305.X86.val5 a0 a1 a2 a3 a4 * VG.Proof.Poly1305.X86.rval r0 q1 q2 q3 =
      (a0 * r0 + 5 * (a1 * q3) + 5 * (a2 * q2) + 5 * (a3 * q1)) +
      2 ^ 32 * (4 * (a0 * q1) + a1 * r0 + 5 * (a2 * q3) + 5 * (a3 * q2) + 5 * (a4 * q1)) +
      2 ^ 64 * (4 * (a0 * q2) + 4 * (a1 * q1) + a2 * r0 + 5 * (a3 * q3) + 5 * (a4 * q2)) +
      2 ^ 96 * (4 * (a0 * q3) + 4 * (a1 * q2) + 4 * (a2 * q1) + a3 * r0 + 5 * (a4 * q3)) +
      2 ^ 128 * (a4 * r0) +
      P * (a1 * q3 + a2 * q2 + a3 * q1 + 2 ^ 32 * (a2 * q3 + a3 * q2 + a4 * q1) +
        2 ^ 64 * (a3 * q3 + a4 * q2) + 2 ^ 96 * (a4 * q3)) := by
  have hP : P + 5 = 2 ^ 130 := by simp only [P, Nat.reducePow, Nat.reduceSub, Nat.reduceAdd]
  have e : VG.Proof.Poly1305.X86.val5 a0 a1 a2 a3 a4 * VG.Proof.Poly1305.X86.rval r0 q1 q2 q3 +
      5 * (a1 * q3 + a2 * q2 + a3 * q1 + 2 ^ 32 * (a2 * q3 + a3 * q2 + a4 * q1) +
        2 ^ 64 * (a3 * q3 + a4 * q2) + 2 ^ 96 * (a4 * q3)) =
      (a0 * r0 + 5 * (a1 * q3) + 5 * (a2 * q2) + 5 * (a3 * q1)) +
      2 ^ 32 * (4 * (a0 * q1) + a1 * r0 + 5 * (a2 * q3) + 5 * (a3 * q2) + 5 * (a4 * q1)) +
      2 ^ 64 * (4 * (a0 * q2) + 4 * (a1 * q1) + a2 * r0 + 5 * (a3 * q3) + 5 * (a4 * q2)) +
      2 ^ 96 * (4 * (a0 * q3) + 4 * (a1 * q2) + 4 * (a2 * q1) + a3 * r0 + 5 * (a4 * q3)) +
      2 ^ 128 * (a4 * r0) +
      2 ^ 130 * (a1 * q3 + a2 * q2 + a3 * q1 + 2 ^ 32 * (a2 * q3 + a3 * q2 + a4 * q1) +
        2 ^ 64 * (a3 * q3 + a4 * q2) + 2 ^ 96 * (a4 * q3)) := by
    simp only [VG.Proof.Poly1305.X86.val5, VG.Proof.Poly1305.X86.rval]; grind
  rw [← hP, Nat.add_mul, ← Nat.add_assoc] at e
  exact Nat.add_right_cancel e

theorem mul_le' {a b c d : Nat} (h₁ : a ≤ b) (h₂ : c ≤ d) : a * c ≤ b * d := Nat.mul_le_mul h₁ h₂

/-- Absorbing a block (`products` and `carry`): from the words `a` of `h + m`
(`a4 ≤ 6`), the sums of products `dk` (each with the carry out of `d(k-1)`)
fit in 64 bits, `d4` in 32, and the result `w = t0 + 2³² t1 + 2⁶⁴ t2 + 2⁹⁶
t3 + 2¹²⁸ (d4 mod 4) + 5 ⌊d4 / 4⌋`, where `tk = dk mod 2³²`, is congruent to
`(h + m) r` modulo `p`, and less than `5 · 2¹²⁸`. -/
theorem absorb_arith {a0 a1 a2 a3 a4 r0 q1 q2 q3 d0 d1 d2 d3 d4 : Nat}
    (ha0 : a0 < 2 ^ 32) (ha1 : a1 < 2 ^ 32) (ha2 : a2 < 2 ^ 32) (ha3 : a3 < 2 ^ 32) (ha4 : a4 ≤ 6)
    (hr0 : r0 < 2 ^ 28) (hq1 : q1 < 2 ^ 26) (hq2 : q2 < 2 ^ 26) (hq3 : q3 < 2 ^ 26)
    (e0 : d0 = 0 + (a0 * r0 + (a1 * (5 * q3) + (a2 * (5 * q2) + (a3 * (5 * q1) + 0)))))
    (e1 : d1 = d0 / 2 ^ 32 + (a0 * (4 * q1) + (a1 * r0 + (a2 * (5 * q3) + (a3 * (5 * q2) +
      (a4 * (5 * q1) + 0))))))
    (e2 : d2 = d1 / 2 ^ 32 + (a0 * (4 * q2) + (a1 * (4 * q1) + (a2 * r0 + (a3 * (5 * q3) +
      (a4 * (5 * q2) + 0))))))
    (e3 : d3 = d2 / 2 ^ 32 + (a0 * (4 * q3) + (a1 * (4 * q2) + (a2 * (4 * q1) + (a3 * r0 +
      (a4 * (5 * q3) + 0))))))
    (e4 : d4 = d3 / 2 ^ 32 + a4 * r0) :
    d0 < 2 ^ 64 ∧ d1 < 2 ^ 64 ∧ d2 < 2 ^ 64 ∧ d3 < 2 ^ 64 ∧ d4 < 2 ^ 32 ∧ 5 * (d4 / 4) < 2 ^ 32 ∧
      (d0 % 2 ^ 32 + 2 ^ 32 * (d1 % 2 ^ 32) + 2 ^ 64 * (d2 % 2 ^ 32) + 2 ^ 96 * (d3 % 2 ^ 32) +
        2 ^ 128 * (d4 % 4) + 5 * (d4 / 4)) % P =
        (VG.Proof.Poly1305.X86.val5 a0 a1 a2 a3 a4 * VG.Proof.Poly1305.X86.rval r0 q1 q2 q3) % P := by
  have e := VG.Proof.Poly1305.X86.fold_identity a0 a1 a2 a3 a4 r0 q1 q2 q3
  -- Every product, bounded.
  have b : ∀ a q, a < 2 ^ 32 → q < 2 ^ 26 → a * q ≤ (2 ^ 32 - 1) * (2 ^ 26 - 1) :=
    fun _ _ h h' => VG.Proof.Poly1305.X86.mul_le' (Nat.le_sub_one_of_lt h) (Nat.le_sub_one_of_lt h')
  have br : ∀ a, a < 2 ^ 32 → a * r0 ≤ (2 ^ 32 - 1) * (2 ^ 28 - 1) :=
    fun _ h => VG.Proof.Poly1305.X86.mul_le' (Nat.le_sub_one_of_lt h) (Nat.le_sub_one_of_lt hr0)
  have p01 := b a0 q1 ha0 hq1; have p02 := b a0 q2 ha0 hq2; have p03 := b a0 q3 ha0 hq3
  have p11 := b a1 q1 ha1 hq1; have p12 := b a1 q2 ha1 hq2; have p13 := b a1 q3 ha1 hq3
  have p21 := b a2 q1 ha2 hq1; have p22 := b a2 q2 ha2 hq2; have p23 := b a2 q3 ha2 hq3
  have p31 := b a3 q1 ha3 hq1; have p32 := b a3 q2 ha3 hq2; have p33 := b a3 q3 ha3 hq3
  have p41 : a4 * q1 ≤ 6 * (2 ^ 26 - 1) := VG.Proof.Poly1305.X86.mul_le' ha4 (Nat.le_sub_one_of_lt hq1)
  have p42 : a4 * q2 ≤ 6 * (2 ^ 26 - 1) := VG.Proof.Poly1305.X86.mul_le' ha4 (Nat.le_sub_one_of_lt hq2)
  have p43 : a4 * q3 ≤ 6 * (2 ^ 26 - 1) := VG.Proof.Poly1305.X86.mul_le' ha4 (Nat.le_sub_one_of_lt hq3)
  have p00 := br a0 ha0; have p10 := br a1 ha1; have p20 := br a2 ha2; have p30 := br a3 ha3
  have p40 : a4 * r0 ≤ 6 * (2 ^ 28 - 1) := VG.Proof.Poly1305.X86.mul_le' ha4 (Nat.le_sub_one_of_lt hr0)
  -- Named products for `omega`.
  have m4 : ∀ a q, a * (4 * q) = 4 * (a * q) := fun a q => Nat.mul_left_comm _ _ _
  have m5 : ∀ a q, a * (5 * q) = 5 * (a * q) := fun a q => Nat.mul_left_comm _ _ _
  rw [m5, m5, m5] at e0
  rw [m4, m5, m5, m5] at e1
  rw [m4, m4, m5, m5] at e2
  rw [m4, m4, m4, m5] at e3
  have hP : P = 2 ^ 130 - 5 := rfl
  have k0 := (Nat.div_add_mod d0 (2 ^ 32)).symm
  generalize d0 / 2 ^ 32 = c0 at k0 e1
  generalize d0 % 2 ^ 32 = t0 at k0 ⊢
  have k1 := (Nat.div_add_mod d1 (2 ^ 32)).symm
  generalize d1 / 2 ^ 32 = c1 at k1 e2
  generalize d1 % 2 ^ 32 = t1 at k1 ⊢
  have k2 := (Nat.div_add_mod d2 (2 ^ 32)).symm
  generalize d2 / 2 ^ 32 = c2 at k2 e3
  generalize d2 % 2 ^ 32 = t2 at k2 ⊢
  have k3 := (Nat.div_add_mod d3 (2 ^ 32)).symm
  generalize d3 / 2 ^ 32 = c3 at k3 e4
  generalize d3 % 2 ^ 32 = t3 at k3 ⊢
  have k4 := (Nat.div_add_mod d4 4).symm
  generalize d4 / 4 = c4 at k4 ⊢
  generalize d4 % 4 = t4 at k4 ⊢
  have b0 : d0 < 2 ^ 63 := by omega_using [e0, p00, p13, p22, p31]
  have C0 : c0 < 2 ^ 31 := by omega_using [b0, k0]
  have b1 : d1 < 2 ^ 63 := by omega_using [C0, e1, p01, p10, p23, p32, p41]
  have C1 : c1 < 2 ^ 31 := by omega_using [b1, k1]
  have b2 : d2 < 2 ^ 63 := by omega_using [C1, e2, p02, p11, p20, p33, p42]
  have C2 : c2 < 2 ^ 31 := by omega_using [b2, k2]
  have b3 : d3 < 2 ^ 62 + 2 ^ 32 := by omega_using [C2, e3, p03, p12, p21, p30, p43]
  have C3 : c3 < 2 ^ 30 + 1 := by omega_using [b3, k3]
  have b4 : d4 < 2 ^ 31 + 2 ^ 30 := by omega_using [C3, e4, p40]
  refine ⟨by omega_using [b0], by omega_using [b1], by omega_using [b2], by omega_using [b3],
    by omega_using [b4], by omega_using [b4, k4], ?_⟩
  rw [e, show ((a0 * r0) + 5 * (a1 * q3) + 5 * (a2 * q2) + 5 * (a3 * q1)) +
      2 ^ 32 * (4 * (a0 * q1) + (a1 * r0) + 5 * (a2 * q3) + 5 * (a3 * q2) + 5 * (a4 * q1)) +
      2 ^ 64 * (4 * (a0 * q2) + 4 * (a1 * q1) + (a2 * r0) + 5 * (a3 * q3) + 5 * (a4 * q2)) +
      2 ^ 96 * (4 * (a0 * q3) + 4 * (a1 * q2) + 4 * (a2 * q1) + (a3 * r0) + 5 * (a4 * q3)) + 2 ^ 128 * (a4 * r0) =
      t0 + 2 ^ 32 * t1 + 2 ^ 64 * t2 + 2 ^ 96 * t3 +
      2 ^ 128 * t4 + 5 * c4 + P * c4 by
        rw [e0, Nat.zero_add] at k0; rw [e1] at k1; rw [e2] at k2; rw [e3] at k3; rw [e4] at k4
        rw [hP]; omega_using [k0, k1, k2, k3, k4],
    Nat.add_assoc _ (P * _), ← Nat.mul_add, Nat.add_mul_mod_self_left]

/-- The words of `h` after a block is absorbed (`carry`): `w` (see
`absorb_arith`) in five words, with carries; the top one is at most 4. -/
theorem carry_arith {t0 t1 t2 t3 d4 e u0 u1 u2 u3 u4 : Nat} (ht0 : t0 < 2 ^ 32)
    (ht1 : t1 < 2 ^ 32) (ht2 : t2 < 2 ^ 32) (ht3 : t3 < 2 ^ 32)
    (he : e < 2 ^ 32) (hu0 : u0 = (e + t0) % 2 ^ 32)
    (hu1 : u1 = (t1 + (e + t0) / 2 ^ 32) % 2 ^ 32)
    (hu2 : u2 = (t2 + (t1 + (e + t0) / 2 ^ 32) / 2 ^ 32) % 2 ^ 32)
    (hu3 : u3 = (t3 + (t2 + (t1 + (e + t0) / 2 ^ 32) / 2 ^ 32) / 2 ^ 32) % 2 ^ 32)
    (hu4 : u4 = (d4 % 4 + (t3 + (t2 + (t1 + (e + t0) / 2 ^ 32) / 2 ^ 32) / 2 ^ 32) / 2 ^ 32) % 2 ^ 32) :
    VG.Proof.Poly1305.X86.val5 u0 u1 u2 u3 u4 = t0 + 2 ^ 32 * t1 + 2 ^ 64 * t2 + 2 ^ 96 * t3 + 2 ^ 128 * (d4 % 4) + e ∧
      u4 ≤ 4 := by
  have k0 := Carry.divMod (e + t0) (2 ^ 32)
  rw [← hu0] at k0
  generalize (e + t0) / 2 ^ 32 = c0 at k0 hu1 hu2 hu3 hu4
  have C0 : c0 < 2 := by omega_using [he, ht0, k0]
  have k1 := Carry.divMod (t1 + c0) (2 ^ 32)
  rw [← hu1] at k1
  generalize (t1 + c0) / 2 ^ 32 = c1 at k1 hu2 hu3 hu4
  have C1 : c1 < 2 := by omega_using [ht1, C0, k1]
  have k2 := Carry.divMod (t2 + c1) (2 ^ 32)
  rw [← hu2] at k2
  generalize (t2 + c1) / 2 ^ 32 = c2 at k2 hu3 hu4
  have C2 : c2 < 2 := by omega_using [ht2, C1, k2]
  have k3 := Carry.divMod (t3 + c2) (2 ^ 32)
  rw [← hu3] at k3
  generalize (t3 + c2) / 2 ^ 32 = c3 at k3 hu4
  have C3 : c3 < 2 := by omega_using [ht3, C2, k3]
  have m4 := Nat.mod_lt d4 (show 0 < 4 by decide)
  generalize d4 % 4 = t4 at m4 hu4 ⊢
  have hu4' := Carry.eq_of_mod hu4 (by omega_using [m4, C3])
  simp only [VG.Proof.Poly1305.X86.val5]
  exact ⟨by omega_using [k0, k1, k2, k3, hu4'], by omega_using [m4, C3, hu4']⟩

/-- Adding a block `m0 + … + 2⁹⁶ m3 + 2¹²⁸ pad` to `h` with `h4 ≤ 4` (`addBlock`):
the words of the sum, the top one at most 6. -/
theorem add_arith {h0 h1 h2 h3 h4 m0 m1 m2 m3 pad u0 u1 u2 u3 u4 : Nat} (hh0 : h0 < 2 ^ 32)
    (hh1 : h1 < 2 ^ 32) (hh2 : h2 < 2 ^ 32) (hh3 : h3 < 2 ^ 32) (hh4 : h4 ≤ 4) (hm0 : m0 < 2 ^ 32)
    (hm1 : m1 < 2 ^ 32) (hm2 : m2 < 2 ^ 32) (hm3 : m3 < 2 ^ 32) (hpad : pad ≤ 1)
    (hu0 : u0 = (h0 + m0) % 2 ^ 32)
    (hu1 : u1 = (h1 + m1 + (h0 + m0) / 2 ^ 32) % 2 ^ 32)
    (hu2 : u2 = (h2 + m2 + (h1 + m1 + (h0 + m0) / 2 ^ 32) / 2 ^ 32) % 2 ^ 32)
    (hu3 : u3 = (h3 + m3 + (h2 + m2 + (h1 + m1 + (h0 + m0) / 2 ^ 32) / 2 ^ 32) / 2 ^ 32) % 2 ^ 32)
    (hu4 : u4 = (h4 + pad + (h3 + m3 + (h2 + m2 + (h1 + m1 + (h0 + m0) / 2 ^ 32) / 2 ^ 32) / 2 ^ 32) /
      2 ^ 32) % 2 ^ 32) :
    VG.Proof.Poly1305.X86.val5 u0 u1 u2 u3 u4 = VG.Proof.Poly1305.X86.val5 h0 h1 h2 h3 h4 + (m0 + 2 ^ 32 * m1 + 2 ^ 64 * m2 + 2 ^ 96 * m3 +
      2 ^ 128 * pad) ∧ u4 ≤ 6 := by
  have k0 := Carry.divMod (h0 + m0) (2 ^ 32)
  rw [← hu0] at k0
  generalize (h0 + m0) / 2 ^ 32 = c0 at k0 hu1 hu2 hu3 hu4
  have C0 : c0 < 2 := by omega_using [hh0, hm0, k0]
  have k1 := Carry.divMod (h1 + m1 + c0) (2 ^ 32)
  rw [← hu1] at k1
  generalize (h1 + m1 + c0) / 2 ^ 32 = c1 at k1 hu2 hu3 hu4
  have C1 : c1 < 2 := by omega_using [hh1, hm1, C0, k1]
  have k2 := Carry.divMod (h2 + m2 + c1) (2 ^ 32)
  rw [← hu2] at k2
  generalize (h2 + m2 + c1) / 2 ^ 32 = c2 at k2 hu3 hu4
  have C2 : c2 < 2 := by omega_using [hh2, hm2, C1, k2]
  have k3 := Carry.divMod (h3 + m3 + c2) (2 ^ 32)
  rw [← hu3] at k3
  generalize (h3 + m3 + c2) / 2 ^ 32 = c3 at k3 hu4
  have C3 : c3 < 2 := by omega_using [hh3, hm3, C2, k3]
  have hu4' := Carry.eq_of_mod hu4 (by omega_using [hh4, hpad, C3])
  simp only [VG.Proof.Poly1305.X86.val5]
  exact ⟨by omega_using [k0, k1, k2, k3, hu4'], by omega_using [hh4, hpad, C3, hu4']⟩

/-- The final reduction (`plus5`, `selectWord`, `selectTop`): `g = h + 5` in
words (`g4` the top one, not reduced), and `b = ⌊g4 / 4⌋`. If `b = 1`, `g -
2¹³⁰` (the words `g0, …, g3, g4 mod 4`) is `h mod p`, and otherwise `h` (whose
top word is `h4 mod 4`) is. -/
theorem reduce_arith {h0 h1 h2 h3 h4 g0 g1 g2 g3 g4 : Nat} (hh0 : h0 < 2 ^ 32)
    (hh1 : h1 < 2 ^ 32) (hh2 : h2 < 2 ^ 32) (hh3 : h3 < 2 ^ 32) (hh4 : h4 ≤ 4)
    (e0 : g0 = (h0 + 5) % 2 ^ 32) (e1 : g1 = (h1 + (h0 + 5) / 2 ^ 32) % 2 ^ 32)
    (e2 : g2 = (h2 + (h1 + (h0 + 5) / 2 ^ 32) / 2 ^ 32) % 2 ^ 32)
    (e3 : g3 = (h3 + (h2 + (h1 + (h0 + 5) / 2 ^ 32) / 2 ^ 32) / 2 ^ 32) % 2 ^ 32)
    (e4 : g4 = (h4 + (h3 + (h2 + (h1 + (h0 + 5) / 2 ^ 32) / 2 ^ 32) / 2 ^ 32) / 2 ^ 32) % 2 ^ 32) :
    (g4 / 4 = 1 ∧ VG.Proof.Poly1305.X86.val5 g0 g1 g2 g3 (g4 % 4) = VG.Proof.Poly1305.X86.val5 h0 h1 h2 h3 h4 % P) ∨
      (g4 / 4 = 0 ∧ VG.Proof.Poly1305.X86.val5 h0 h1 h2 h3 (h4 % 4) = VG.Proof.Poly1305.X86.val5 h0 h1 h2 h3 h4 % P) := by
  have hP : P = 2 ^ 130 - 5 := rfl
  have k0 := (Nat.div_add_mod (h0 + 5) (2 ^ 32)).symm
  rw [← e0] at k0
  generalize (h0 + 5) / 2 ^ 32 = c0 at k0 e1 e2 e3 e4
  have C0 : c0 < 2 := by omega_using [hh0, k0]
  have k1 := (Nat.div_add_mod (h1 + c0) (2 ^ 32)).symm
  rw [← e1] at k1
  generalize (h1 + c0) / 2 ^ 32 = c1 at k1 e2 e3 e4
  have C1 : c1 < 2 := by omega_using [hh1, C0, k1]
  have k2 := (Nat.div_add_mod (h2 + c1) (2 ^ 32)).symm
  rw [← e2] at k2
  generalize (h2 + c1) / 2 ^ 32 = c2 at k2 e3 e4
  have C2 : c2 < 2 := by omega_using [hh2, C1, k2]
  have k3 := (Nat.div_add_mod (h3 + c2) (2 ^ 32)).symm
  rw [← e3] at k3
  generalize (h3 + c2) / 2 ^ 32 = c3 at k3 e4
  have C3 : c3 < 2 := by omega_using [hh3, C2, k3]
  have g4e : g4 = h4 + c3 := e4.trans (Nat.mod_eq_of_lt (by omega_using [hh4, C3]))
  have hg : VG.Proof.Poly1305.X86.val5 g0 g1 g2 g3 g4 = VG.Proof.Poly1305.X86.val5 h0 h1 h2 h3 h4 + 5 := by
    simp only [VG.Proof.Poly1305.X86.val5]; omega_using [k0, k1, k2, k3, g4e]
  have hb : g0 < 2 ^ 32 ∧ g1 < 2 ^ 32 ∧ g2 < 2 ^ 32 ∧ g3 < 2 ^ 32 ∧ g4 ≤ 5 :=
    ⟨e0 ▸ Nat.mod_lt _ (by decide), e1 ▸ Nat.mod_lt _ (by decide), e2 ▸ Nat.mod_lt _ (by decide),
      e3 ▸ Nat.mod_lt _ (by decide), by omega_using [hh4, C3, g4e]⟩
  simp only [VG.Proof.Poly1305.X86.val5] at hg
  rcases (by omega_using [hb] : g4 / 4 = 1 ∨ g4 / 4 = 0) with h | h
  · left
    refine ⟨h, ?_⟩
    have m4 : g4 % 4 = g4 - 4 := by omega_using [h]
    have lt : VG.Proof.Poly1305.X86.val5 g0 g1 g2 g3 (g4 % 4) < P := by
      rw [hP]; simp only [VG.Proof.Poly1305.X86.val5]; omega_using [hb, h, m4]
    have e : VG.Proof.Poly1305.X86.val5 h0 h1 h2 h3 h4 = VG.Proof.Poly1305.X86.val5 g0 g1 g2 g3 (g4 % 4) + P := by
      rw [hP]; simp only [VG.Proof.Poly1305.X86.val5]; omega_using [hg, m4, h]
    rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt lt]
  · right
    refine ⟨h, ?_⟩
    have m4 : h4 % 4 = h4 := Nat.mod_eq_of_lt (by omega_using [h, g4e])
    have lt : VG.Proof.Poly1305.X86.val5 h0 h1 h2 h3 h4 < P := by rw [hP]; simp only [VG.Proof.Poly1305.X86.val5]; omega_using [hg, hb, h]
    rw [m4, Nat.mod_eq_of_lt lt]

/-- The tag's words (`addS`): `x + s` modulo `2¹²⁸`, in four words, with carries. -/
theorem addS_arith {x0 x1 x2 x3 s0 s1 s2 s3 : Nat} (X S : Nat)
    (hX : X % 2 ^ 128 = x0 + 2 ^ 32 * x1 + 2 ^ 64 * x2 + 2 ^ 96 * x3)
    (hS : S = s0 + 2 ^ 32 * s1 + 2 ^ 64 * s2 + 2 ^ 96 * s3) :
    (x0 + s0) % 2 ^ 32 = (X + S) % 2 ^ 32 ∧
    (x1 + s1 + (x0 + s0) / 2 ^ 32) % 2 ^ 32 = (X + S) / 2 ^ 32 % 2 ^ 32 ∧
    (x2 + s2 + (x1 + s1 + (x0 + s0) / 2 ^ 32) / 2 ^ 32) % 2 ^ 32 = (X + S) / 2 ^ 64 % 2 ^ 32 ∧
    (x3 + s3 + (x2 + s2 + (x1 + s1 + (x0 + s0) / 2 ^ 32) / 2 ^ 32) / 2 ^ 32) % 2 ^ 32 =
      (X + S) / 2 ^ 96 % 2 ^ 32 := by
  subst hS
  have k := Carry.divMod X (2 ^ 128)
  rw [hX] at k
  generalize X / 2 ^ 128 = Q at k
  have k0 := Carry.divMod (x0 + s0) (2 ^ 32)
  have m0 := Nat.mod_lt (x0 + s0) (show 0 < 2 ^ 32 by decide)
  generalize (x0 + s0) / 2 ^ 32 = c0 at k0 ⊢
  generalize (x0 + s0) % 2 ^ 32 = u0 at k0 m0 ⊢
  have k1 := Carry.divMod (x1 + s1 + c0) (2 ^ 32)
  have m1 := Nat.mod_lt (x1 + s1 + c0) (show 0 < 2 ^ 32 by decide)
  generalize (x1 + s1 + c0) / 2 ^ 32 = c1 at k1 ⊢
  generalize (x1 + s1 + c0) % 2 ^ 32 = u1 at k1 m1 ⊢
  have k2 := Carry.divMod (x2 + s2 + c1) (2 ^ 32)
  have m2 := Nat.mod_lt (x2 + s2 + c1) (show 0 < 2 ^ 32 by decide)
  generalize (x2 + s2 + c1) / 2 ^ 32 = c2 at k2 ⊢
  generalize (x2 + s2 + c1) % 2 ^ 32 = u2 at k2 m2 ⊢
  have k3 := Carry.divMod (x3 + s3 + c2) (2 ^ 32)
  have m3 := Nat.mod_lt (x3 + s3 + c2) (show 0 < 2 ^ 32 by decide)
  generalize (x3 + s3 + c2) / 2 ^ 32 = c3 at k3 ⊢
  generalize (x3 + s3 + c2) % 2 ^ 32 = u3 at k3 m3 ⊢
  have eN : X + (s0 + 2 ^ 32 * s1 + 2 ^ 64 * s2 + 2 ^ 96 * s3) =
      u0 + 2 ^ 32 * (u1 + 2 ^ 32 * (u2 + 2 ^ 32 * (u3 + 2 ^ 32 * (c3 + Q)))) := by
    omega_using [k, k0, k1, k2, k3]
  rw [show (2 : Nat) ^ 96 = 2 ^ 32 * 2 ^ 32 * 2 ^ 32 from rfl,
    show (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 from rfl, ← Nat.div_div_eq_div_mul,
    ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, eN, (Carry.digit _ m0).1,
    (Carry.digit _ m0).2, (Carry.digit _ m1).1, (Carry.digit _ m1).2, (Carry.digit _ m2).1,
    (Carry.digit _ m2).2, (Carry.digit _ m3).1]
  exact ⟨rfl, rfl, rfl, rfl⟩

end VG.Proof.Poly1305.X86

end

/-!
# Poly1305 on x86 (32-bit): the steps of the code

Each lemma runs a few instructions symbolically and states their effect on the
numbers in the registers and the words in memory.
-/

namespace VG.Proof.Poly1305.X86

open VG VG.X86 VG.Impl.Poly1305.X86

/-- Two states agree except on the registers `rs` (and the flags), in memory
and regions. -/
def Keeps (rs : List Reg) (s s' : State) : Prop :=
  (∀ r, r ∉ rs → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr

theorem Keeps.gpr' {rs : List Reg} {s s' : State} (h : VG.Proof.Poly1305.X86.Keeps rs s s') {r : Reg}
    (hr : r ∉ rs := by decide) : s'.gpr r = s.gpr r := h.1 r hr

theorem Keeps.trans {rs rs' : List Reg} {s₁ s₂ s₃ : State} (h₁ : VG.Proof.Poly1305.X86.Keeps rs s₁ s₂)
    (h₂ : VG.Proof.Poly1305.X86.Keeps rs' s₂ s₃) : VG.Proof.Poly1305.X86.Keeps (rs ++ rs') s₁ s₃ :=
  ⟨fun r hr => by
    rw [List.mem_append, not_or] at hr
    rw [h₂.1 r hr.2, h₁.1 r hr.1],
   h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1, h₂.2.2.2.trans h₁.2.2.2⟩

theorem Keeps.mono {rs rs' : List Reg} {s s' : State} (h : VG.Proof.Poly1305.X86.Keeps rs s s')
    (hs : ∀ r ∈ rs, r ∈ rs' := by decide) : VG.Proof.Poly1305.X86.Keeps rs' s s' :=
  ⟨fun r hr => h.1 r fun h' => hr (hs r h'), h.2⟩

theorem Keeps.refl (rs : List Reg) (s : State) : VG.Proof.Poly1305.X86.Keeps rs s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

/-- The value of a register, as a number. -/
abbrev v (s : State) (r : Reg) : Nat := (s.gpr r).toNat

/-- The 32-bit word at `[x + d]`. -/
abbrev wd (m : Mem) (x : BitVec 32) (d : Nat) : BitVec 32 := m.readW (addr x d) 32

/-- The same, as a number. -/
abbrev wv (m : Mem) (x : BitVec 32) (d : Nat) : Nat := (VG.Proof.Poly1305.X86.wd m x d).toNat

/-! ## Addresses and regions -/

theorem addr_toNat {x : BitVec 32} {d : Nat} (h : x.toNat + d < 2 ^ 32) :
    (addr x d).toNat = x.toNat + d := by
  rw [addr_eq h, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have := x.isLt
  rw [Nat.mod_eq_of_lt (a := x.toNat) (by omega_using []), Nat.mod_eq_of_lt (a := d) (by omega_using [h])]
  exact Nat.mod_eq_of_lt (by omega_using [h])

/-- The region of `n` bytes at `[x + d]`. -/
abbrev sub (x : BitVec 32) (d n : Nat) : Region := ⟨addr x d, n⟩

theorem sub_contains {x : BitVec 32} {a k d n : Nat} (hx : x.toNat + a + k ≤ 2 ^ 32) (h₁ : a ≤ d)
    (h₂ : d + n ≤ a + k) (hn : 0 < n) : (VG.Proof.Poly1305.X86.sub x a k).Contains (addr x d) n := by
  rw [VG.Proof.Poly1305.X86.sub, addr_eq (by omega_using [hx, h₁, h₂, hn]), addr_eq (by omega_using [hx, h₂, hn])]
  exact Offset.contains _ h₁ h₂ (by omega_using [hx])

theorem sub_disj {x : BitVec 32} {d n e k : Nat} (hd : x.toNat + d + n ≤ 2 ^ 32)
    (he : x.toNat + e + k ≤ 2 ^ 32) (h : d + n ≤ e ∨ e + k ≤ d) : (VG.Proof.Poly1305.X86.sub x d n).Disjoint (VG.Proof.Poly1305.X86.sub x e k) := by
  intro a h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) h₁
  have hk : 0 < k := Nat.lt_of_le_of_lt (Nat.zero_le _) h₂
  rw [addr_eq (by omega_using [hd, hn])] at h₁
  rw [addr_eq (by omega_using [he, hk])] at h₂
  exact Offset.disjoint _ h (by omega_using [hd]) (by omega_using [he]) a h₁ h₂

/-- The 32-bit word at `[x + d]`, after a store at `[x + e]` that does not overlap it. -/
theorem wd_write_ne (m : Mem) {x : BitVec 32} (w : BitVec 32) {d e : Nat}
    (hd : x.toNat + d + 4 ≤ 2 ^ 32) (he : x.toNat + e + 4 ≤ 2 ^ 32) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    VG.Proof.Poly1305.X86.wd (m.writeW (addr x e) w) x d = VG.Proof.Poly1305.X86.wd m x d :=
  Mem.readW_writeW_sep ((VG.Proof.Poly1305.X86.sub_disj hd he h).sep (Region.contains_self _ _) (Region.contains_self _ _))
    (by decide)

theorem wd_write_self (m : Mem) (x : BitVec 32) (w : BitVec 32) (d : Nat) :
    VG.Proof.Poly1305.X86.wd (m.writeW (addr x d) w) x d = w :=
  Mem.readW_writeW_self32 _ _ _

/-- A word outside the regions a frame allows to change. -/
theorem wd_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {x : BitVec 32} {d : Nat}
    (hd : ∀ r ∈ rs, (VG.Proof.Poly1305.X86.sub x d 4).Disjoint r) : VG.Proof.Poly1305.X86.wd m' x d = VG.Proof.Poly1305.X86.wd m x d :=
  hf.readW (Region.contains_self _ _) hd (by decide)

/-- The state's region. -/
abbrev sR (st : BitVec 32) : Region := ⟨st.setWidth 64, 128⟩

theorem sR_contains {st : BitVec 32} (hst : st.toNat + 128 ≤ 2 ^ 32) {d n : Nat} (h : d + n ≤ 128)
    (hn : 0 < n) : (VG.Proof.Poly1305.X86.sR st).Contains (addr st d) n := by
  have := VG.Proof.Poly1305.X86.sub_contains (x := st) (a := 0) (k := 128) (by omega_using [hst]) (Nat.zero_le d) (by omega_using [h]) hn
  simpa [VG.Proof.Poly1305.X86.sub, addr] using this

/-- The code's view of the state: `edi` points at it, it is writable, and it
does not wrap around the 32-bit address space. -/
structure Ctx (st : BitVec 32) (s : State) : Prop where
  edi : s.gpr .edi = st
  fit : st.toNat + 128 ≤ 2 ^ 32
  wr : VG.Proof.Poly1305.X86.sR st ∈ s.wr

namespace Ctx
variable {st : BitVec 32} {s : State} (h : VG.Proof.Poly1305.X86.Ctx st s)
include h

theorem inW {d n : Nat} (hd : d + n ≤ 128) (hn : 0 < n) : InRegions s.wr (addr st d) n :=
  ⟨_, h.wr, VG.Proof.Poly1305.X86.sR_contains h.fit hd hn⟩

theorem inRW {d n : Nat} (hd : d + n ≤ 128) (hn : 0 < n) :
    InRegions (s.rd ++ s.wr) (addr st d) n :=
  ⟨_, List.mem_append_right _ h.wr, VG.Proof.Poly1305.X86.sR_contains h.fit hd hn⟩

theorem inW' {d : Nat} (hd : d + 4 ≤ 128) : InRegions s.wr (addr (s.gpr .edi) d) 4 := by
  rw [h.edi]; exact h.inW hd (by decide)

theorem inRW' {d : Nat} (hd : d + 4 ≤ 128) : InRegions (s.rd ++ s.wr) (addr (s.gpr .edi) d) 4 := by
  rw [h.edi]; exact h.inRW hd (by decide)

/-- The context survives a change of other registers and of memory. -/
theorem keep {s' : State} (he : s'.gpr .edi = s.gpr .edi) (hw : s'.wr = s.wr) : VG.Proof.Poly1305.X86.Ctx st s' :=
  ⟨he.trans h.edi, h.fit, hw ▸ h.wr⟩

theorem wd_ne (m : Mem) (w : BitVec 32) {d e : Nat} (hd : d + 4 ≤ 128) (he : e + 4 ≤ 128)
    (hde : d + 4 ≤ e ∨ e + 4 ≤ d) : VG.Proof.Poly1305.X86.wd (m.writeW (addr st e) w) st d = VG.Proof.Poly1305.X86.wd m st d :=
  VG.Proof.Poly1305.X86.wd_write_ne m w (by have := h.fit; omega_using [hd, this]) (by have := h.fit; omega_using [he, this]) hde

end Ctx

/-- The accumulator of a sum of products, `ebx + 2³² ebp`. -/
abbrev acc (s : State) : Nat := VG.Proof.Poly1305.X86.v s .ebx + 2 ^ 32 * VG.Proof.Poly1305.X86.v s .ebp

theorem ea_at (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = addr (s.gpr b) d := rfl

theorem carry_toNat (c : Bool) : ((BitVec.ofBool c).setWidth 32).toNat = c.toNat := by
  cases c <;> rfl

theorem toNat_mul_lo (a b : BitVec 32) :
    (BitVec.ofNat 32 (a.toNat * b.toNat)).toNat +
      2 ^ 32 * (BitVec.ofNat 32 (a.toNat * b.toNat / 2 ^ 32)).toNat = a.toNat * b.toNat := by
  have := Nat.mul_lt_mul_of_lt_of_lt a.isLt b.isLt
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := _ / 2 ^ 32) (by rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]; omega_using [this])]
  omega_using []

/-- An addition with carry into a second word, as numbers, when the sum fits. -/
theorem add_adc_toNat (a b c d : BitVec 32)
    (h : a.toNat + b.toNat + 2 ^ 32 * (c.toNat + d.toNat) < 2 ^ 64) :
    (a + b).toNat + 2 ^ 32 * (c + d + (BitVec.ofBool (decide (2 ^ 32 ≤ a.toNat + b.toNat))).setWidth 32).toNat =
      a.toNat + b.toNat + 2 ^ 32 * (c.toNat + d.toNat) := by
  simp only [BitVec.toNat_add, VG.Proof.Poly1305.X86.carry_toNat]
  have ha := a.isLt; have hb := b.isLt; have hc := c.isLt; have hd := d.isLt
  by_cases h2 : 2 ^ 32 ≤ a.toNat + b.toNat <;> simp only [h2, decide_true, decide_false,
    Bool.toNat_true, Bool.toNat_false] <;> omega_using [h, h2]

/-- `ebx:ebp += hi · c`, the coefficient `c` at `[edi + off]`. -/
theorem mac_ok (s : State) (i off : Nat)
    (h1 : InRegions (s.rd ++ s.wr) (addr (s.gpr .edi) (hOff i)) 4)
    (h2 : InRegions (s.rd ++ s.wr) (addr (s.gpr .edi) off) 4) :
    WP isa (.block (mac i off)) s fun s' =>
      (VG.Proof.Poly1305.X86.acc s + VG.Proof.Poly1305.X86.wv s.mem (s.gpr .edi) (hOff i) * VG.Proof.Poly1305.X86.wv s.mem (s.gpr .edi) off < 2 ^ 64 →
        VG.Proof.Poly1305.X86.acc s' = VG.Proof.Poly1305.X86.acc s + VG.Proof.Poly1305.X86.wv s.mem (s.gpr .edi) (hOff i) * VG.Proof.Poly1305.X86.wv s.mem (s.gpr .edi) off) ∧
      VG.Proof.Poly1305.X86.Keeps [.eax, .ecx, .edx, .ebx, .ebp] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [mac, runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, VG.Proof.Poly1305.X86.ea_at, VG.Proof.Poly1305.X86.acc, VG.Proof.Poly1305.X86.v, VG.Proof.Poly1305.X86.wv, VG.Proof.Poly1305.X86.wd, State.load32, execMul, execAlu, arithFlags, State.setReg, State.setFlags, h1, h2,
    ite_true, ite_false, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun hlt => ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have e := VG.Proof.Poly1305.X86.toNat_mul_lo (s.mem.readW (addr (s.gpr .edi) (hOff i)) 32)
      (s.mem.readW (addr (s.gpr .edi) off) 32)
    rw [VG.Proof.Poly1305.X86.add_adc_toNat _ _ _ _ (by have := (s.gpr .ebp).isLt; omega_using [hlt, e])]
    omega_using [e]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.2.2.2.2, ↓reduceIte, hr.2.2.2.1, hr.2.2.1, hr.1, hr.2.1]

/-- A chain of `mac`s. -/
theorem macs_ok (L : List (Nat × Nat)) (s : State)
    (hL : ∀ p ∈ L, InRegions (s.rd ++ s.wr) (addr (s.gpr .edi) (hOff p.1)) 4 ∧
      InRegions (s.rd ++ s.wr) (addr (s.gpr .edi) p.2) 4) :
    WP isa (.block (L.flatMap fun p => mac p.1 p.2)) s fun s' =>
      (VG.Proof.Poly1305.X86.acc s + (L.map fun p => VG.Proof.Poly1305.X86.wv s.mem (s.gpr .edi) (hOff p.1) * VG.Proof.Poly1305.X86.wv s.mem (s.gpr .edi) p.2).sum <
          2 ^ 64 →
        VG.Proof.Poly1305.X86.acc s' = VG.Proof.Poly1305.X86.acc s + (L.map fun p => VG.Proof.Poly1305.X86.wv s.mem (s.gpr .edi) (hOff p.1) * VG.Proof.Poly1305.X86.wv s.mem (s.gpr .edi) p.2).sum) ∧
      VG.Proof.Poly1305.X86.Keeps [.eax, .ecx, .edx, .ebx, .ebp] s s' := by
  induction L generalizing s with
  | nil => exact WP.block_nil ⟨fun _ => by simp, Keeps.refl _ _⟩
  | cons p L ih =>
    obtain ⟨h1, h2⟩ := hL p List.mem_cons_self
    rw [List.flatMap_cons]
    refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86.mac_ok s p.1 p.2 h1 h2) fun s₁ ⟨e₁, k₁⟩ => ?_)
    have edi₁ : s₁.gpr .edi = s.gpr .edi := k₁.gpr'
    have hL' : ∀ q ∈ L, InRegions (s₁.rd ++ s₁.wr) (addr (s₁.gpr .edi) (hOff q.1)) 4 ∧
        InRegions (s₁.rd ++ s₁.wr) (addr (s₁.gpr .edi) q.2) 4 := fun q hq => by
      rw [k₁.2.2.1, k₁.2.2.2, edi₁]; exact hL q (List.mem_cons_of_mem _ hq)
    refine WP.mono (ih s₁ hL') fun s₂ ⟨e₂, k₂⟩ => ⟨fun hlt => ?_, (k₁.trans k₂).mono (by simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, reduceCtorEq, or_self, or_true, imp_self, implies_true, and_self])⟩
    rw [edi₁, k₁.2.1] at e₂
    simp only [List.map_cons, List.sum_cons] at hlt ⊢
    rw [e₂ (by rw [e₁ (by omega_using [hlt])]; omega_using [hlt]), e₁ (by omega_using [hlt])]
    omega_using []


/-! ## One instruction at a time

Continuation-style rules that expose only what an instruction changes. -/

/-- `s'` is `s` with register `d` set to `w` (the flags aside). -/
structure Upd (s s' : State) (d : Reg) (w : BitVec 32) : Prop where
  gpr : s'.gpr d = w
  other : ∀ r, r ≠ d → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Upd.setReg (s : State) (d : Reg) (w : BitVec 32) : VG.Proof.Poly1305.X86.Upd s (s.setReg d w) d w :=
  ⟨by simp only [State.setReg, ↓reduceIte], fun r h => by simp only [State.setReg, h, ↓reduceIte], rfl, rfl, rfl⟩

theorem Upd.flags (s : State) (d : Reg) (x : BitVec 32) (c o : Bool) (w : BitVec 32) :
    VG.Proof.Poly1305.X86.Upd s ((arithFlags s x c o).setReg d w) d w :=
  ⟨by simp only [State.setReg, Taint.arithFlags_gpr, Taint.arithFlags_cf, Taint.arithFlags_zf, BitVec.ofNat_eq_ofNat, Taint.arithFlags_sf, Taint.arithFlags_of, Taint.arithFlags_mem, Taint.arithFlags_wr, ↓reduceIte], fun r h => by simp only [State.setReg, arithFlags, State.setFlags, BitVec.ofNat_eq_ofNat, h, ↓reduceIte], rfl, rfl, rfl⟩

theorem Upd.setFlags (s : State) (d : Reg) (c o z n : Option Bool) (w : BitVec 32) :
    VG.Proof.Poly1305.X86.Upd s ((s.setFlags c o z n).setReg d w) d w :=
  ⟨by simp only [State.setReg, ↓reduceIte], fun r h => by simp only [State.setReg, State.setFlags, h, ↓reduceIte], rfl, rfl, rfl⟩

/-- `s'` is `s` with memory `m` (the flags aside). -/
structure Mupd (s s' : State) (m : Mem) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = m
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  cf : s'.cf = s.cf
  zf : s'.zf = s.zf

theorem WP.cons {i : Instr} {is : List Instr} {s s' : State} {Q : State → Prop}
    (h : exec i s = some s') (k : WP isa (.block is) s' Q) : WP isa (.block (i :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨s', h, k⟩

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_mov {d r : Reg} (k : ∀ s', VG.Proof.Poly1305.X86.Upd s s' d (s.gpr r) → s'.cf = s.cf → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _) rfl)

theorem wp_movi {d : Reg} {w : BitVec 32}
    (k : ∀ s', VG.Proof.Poly1305.X86.Upd s s' d w → s'.cf = s.cf → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.imm w) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _) rfl)

theorem wp_movm {d : Reg} {m : MemOp} {a : Addr} (ha : s.ea m = a) (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', VG.Proof.Poly1305.X86.Upd s s' d (s.mem.readW a 32) → s'.cf = s.cf → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.mem m) :: is)) s Q := by
  refine WP.cons (s' := s.setReg d (s.mem.readW a 32)) ?_ (k _ (Upd.setReg _ _ _) rfl)
  simp only [exec, readSrc, State.load32, ha, hin, ↓reduceIte, Option.map_some]

theorem wp_store {m : MemOp} {r : Reg} {a : Addr} (ha : s.ea m = a) (hout : InRegions s.wr a 4)
    (k : ∀ s', VG.Proof.Poly1305.X86.Mupd s s' (s.mem.writeW a (s.gpr r)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store m r :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a (s.gpr r) }) ?_ (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
  simp only [exec, State.store32, ha, hout, ↓reduceIte]

/-- `add d, src` for a source of value `x`: the sum, and its carry out. -/
theorem wp_addx {d : Reg} {src : Src} {x : BitVec 32} (hx : readSrc s src = some x)
    (k : ∀ s', VG.Proof.Poly1305.X86.Upd s s' d (s.gpr d + x) → s'.cf = some (decide (2 ^ 32 ≤ (s.gpr d).toNat + x.toNat)) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d src :: is)) s Q := by
  refine WP.cons ?_ (k _ (Upd.flags s d (s.gpr d + x) (decide (2 ^ 32 ≤ (s.gpr d).toNat + x.toNat))
    (addOverflow (s.gpr d) x (s.gpr d + x)) _) rfl)
  simp only [exec, execAlu, hx, Option.bind_some]

/-- `adc d, src` for a source of value `x`, with the carry `c` in: the sum,
and its carry out. -/
theorem wp_adcx {d : Reg} {src : Src} {x : BitVec 32} {c : Bool} (hx : readSrc s src = some x)
    (hc : s.cf = some c)
    (k : ∀ s', VG.Proof.Poly1305.X86.Upd s s' d (s.gpr d + x + (BitVec.ofBool c).setWidth 32) →
      s'.cf = some (decide (2 ^ 32 ≤ (s.gpr d).toNat + x.toNat + c.toNat)) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .adc d src :: is)) s Q := by
  refine WP.cons ?_ (k _ (Upd.flags s d (s.gpr d + x + (BitVec.ofBool c).setWidth 32)
    (decide (2 ^ 32 ≤ (s.gpr d).toNat + x.toNat + c.toNat))
    (addOverflow (s.gpr d) x (s.gpr d + x + (BitVec.ofBool c).setWidth 32)) _) rfl)
  simp only [exec, execAlu, hx, Option.bind_some, hc, Option.map_some]

theorem wp_andx {d : Reg} {src : Src} {x : BitVec 32} (hx : readSrc s src = some x)
    (k : ∀ s', VG.Proof.Poly1305.X86.Upd s s' d (s.gpr d &&& x) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .and d src :: is)) s Q := by
  refine WP.cons ?_ (k _ (Upd.flags s d (s.gpr d &&& x) false false _))
  simp only [exec, execAlu, hx, Option.bind_some]

theorem wp_xorx {d : Reg} {src : Src} {x : BitVec 32} (hx : readSrc s src = some x)
    (k : ∀ s', VG.Proof.Poly1305.X86.Upd s s' d (s.gpr d ^^^ x) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .xor d src :: is)) s Q := by
  refine WP.cons ?_ (k _ (Upd.flags s d (s.gpr d ^^^ x) false false _))
  simp only [exec, execAlu, hx, Option.bind_some]

theorem wp_subx {d : Reg} {src : Src} {x : BitVec 32} (hx : readSrc s src = some x)
    (k : ∀ s', VG.Proof.Poly1305.X86.Upd s s' d (s.gpr d - x) → s'.zf = some (s.gpr d - x == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .sub d src :: is)) s Q := by
  refine WP.cons ?_ (k _ (Upd.flags s d (s.gpr d - x) (decide ((s.gpr d).toNat < x.toNat))
    (subOverflow (s.gpr d) x (s.gpr d - x)) _) rfl)
  simp only [exec, execAlu, hx, Option.bind_some]

/-- `cmp d, src` for a source of value `x`: ZF and CF of `d - x`. -/
theorem wp_cmpx {d : Reg} {src : Src} {x : BitVec 32} (hx : readSrc s src = some x)
    (k : ∀ s', VG.Proof.Poly1305.X86.Keeps [] s s' → s'.zf = some (s.gpr d - x == 0) →
      s'.cf = some (decide ((s.gpr d).toNat < x.toNat)) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .cmp d src :: is)) s Q := by
  refine WP.cons ?_ (k (arithFlags s (s.gpr d - x) (decide ((s.gpr d).toNat < x.toNat))
    (subOverflow (s.gpr d) x (s.gpr d - x))) ⟨fun _ _ => rfl, rfl, rfl, rfl⟩ rfl rfl)
  simp only [exec, execAlu, hx, Option.bind_some]

theorem wp_test {d : Reg}
    (k : ∀ s', VG.Proof.Poly1305.X86.Keeps [] s s' → s'.zf = some (s.gpr d &&& s.gpr d == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .test d (.reg d) :: is)) s Q :=
  WP.cons rfl (k _ ⟨fun _ _ => rfl, rfl, rfl, rfl⟩ rfl)

theorem wp_shr {d : Reg} {n : Nat} (hn : 1 ≤ n ∧ n ≤ 31)
    (k : ∀ s', VG.Proof.Poly1305.X86.Upd s s' d (s.gpr d >>> n) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .shr d n :: is)) s Q :=
  WP.cons (by simp only [exec, execShift, hn, and_self, ite_true]; rfl) (k _ (Upd.setFlags _ _ _ _ _ _ _))

theorem wp_movzx8 {d : Reg} {m : MemOp} {a : Addr} (ha : s.ea m = a) (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ s', VG.Proof.Poly1305.X86.Upd s s' d ((s.mem a).setWidth 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movzx8 d m :: is)) s Q := by
  refine WP.cons (s' := s.setReg d ((s.mem a).setWidth 32)) ?_ (k _ (Upd.setReg _ _ _))
  simp only [exec, State.load8, ha, hin, ↓reduceIte, Option.map_some]

theorem wp_store8 {m : MemOp} {r : Reg8} {a : Addr} (ha : s.ea m = a) (hout : InRegions s.wr a 1)
    (k : ∀ s', VG.Proof.Poly1305.X86.Mupd s s' (s.mem.writeW a ((s.gpr r.reg).setWidth 8)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store8 m r :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr r.reg).setWidth 8) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
  simp only [exec, State.store8, ha, hout, ↓reduceIte]

end

theorem readSrc_imm (s : State) (w : BitVec 32) : readSrc s (.imm w) = some w := rfl
theorem readSrc_reg (s : State) (r : Reg) : readSrc s (.reg r) = some (s.gpr r) := rfl

theorem readSrc_mem {s : State} {m : MemOp} {a : Addr} (ha : s.ea m = a)
    (hin : InRegions (s.rd ++ s.wr) a 4) : readSrc s (.mem m) = some (s.mem.readW a 32) := by
  simp only [readSrc, State.load32, ha, hin, ↓reduceIte]

theorem add3_toNat (a b : BitVec 32) (c : Bool) :
    (a + b + (BitVec.ofBool c).setWidth 32).toNat = (a.toNat + b.toNat + c.toNat) % 2 ^ 32 := by
  rw [BitVec.toNat_add, BitVec.toNat_add, VG.Proof.Poly1305.X86.carry_toNat, Nat.mod_add_mod]


/-! ## The state as words

The state's 32 words, as numbers, are a function `f`; a store of a word
updates it (`upd`). -/

/-- The state's words at `st` are `f`. -/
def Words (m : Mem) (st : BitVec 32) (f : Nat → Nat) : Prop := ∀ k < 32, VG.Proof.Poly1305.X86.wv m st (4 * k) = f k

/-- `f` with word `j` replaced by `x`. -/
def upd (f : Nat → Nat) (j x : Nat) : Nat → Nat := fun k => if k = j then x else f k

theorem upd_same (f : Nat → Nat) (j x : Nat) : VG.Proof.Poly1305.X86.upd f j x j = x := by simp only [VG.Proof.Poly1305.X86.upd, ↓reduceIte]

theorem upd_ne (f : Nat → Nat) {j k : Nat} (x : Nat) (h : k ≠ j) : VG.Proof.Poly1305.X86.upd f j x k = f k := by simp only [VG.Proof.Poly1305.X86.upd, h, ↓reduceIte]

theorem Words.write {m : Mem} {st : BitVec 32} {f : Nat → Nat} (h : VG.Proof.Poly1305.X86.Words m st f)
    (hfit : st.toNat + 128 ≤ 2 ^ 32) {j : Nat} (hj : j < 32) (w : BitVec 32) :
    VG.Proof.Poly1305.X86.Words (m.writeW (addr st (4 * j)) w) st (VG.Proof.Poly1305.X86.upd f j w.toNat) := by
  intro k hk
  by_cases e : k = j
  · subst e; rw [VG.Proof.Poly1305.X86.upd_same, VG.Proof.Poly1305.X86.wv, VG.Proof.Poly1305.X86.wd_write_self]
  · rw [VG.Proof.Poly1305.X86.upd_ne _ _ e, VG.Proof.Poly1305.X86.wv, VG.Proof.Poly1305.X86.wd_write_ne m w (by omega_using [hfit, hk]) (by omega_using [hfit, hj]) (by omega_using [e])]; exact h k hk

theorem Words.readW {m : Mem} {st : BitVec 32} {f : Nat → Nat} (h : VG.Proof.Poly1305.X86.Words m st f) {k : Nat}
    (hk : k < 32) : (m.readW (addr st (4 * k)) 32).toNat = f k := h k hk

theorem Words.lt {m : Mem} {st : BitVec 32} {f : Nat → Nat} (h : VG.Proof.Poly1305.X86.Words m st f) {k : Nat}
    (hk : k < 32) : f k < 2 ^ 32 := by
  rw [← h k hk]; exact BitVec.isLt _

/-- Stores to the state stay in its region. -/
theorem frame_write {m m' : Mem} {st : BitVec 32} (hf : Frame [VG.Proof.Poly1305.X86.sR st] m m')
    (hfit : st.toNat + 128 ≤ 2 ^ 32) {d : Nat} (hd : d + 4 ≤ 128) (w : BitVec 32) :
    Frame [VG.Proof.Poly1305.X86.sR st] m (m'.writeW (addr st d) w) :=
  hf.writeW (List.mem_singleton_self _) _ (VG.Proof.Poly1305.X86.sR_contains hfit hd (by decide))

/-- What code leaves that writes only the state: its words `g`, the rest of
memory, the registers but `rs`, and the regions. -/
structure After (st : BitVec 32) (s s' : State) (g : Nat → Nat) (rs : List Reg) : Prop where
  words : VG.Proof.Poly1305.X86.Words s'.mem st g
  frame : Frame [VG.Proof.Poly1305.X86.sR st] s.mem s'.mem
  gpr : ∀ r, r ∉ rs → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

namespace After
variable {st : BitVec 32} {s s₁ s₂ : State} {g g₁ g₂ : Nat → Nat} {rs rs₁ rs₂ : List Reg}

theorem ctx (h : VG.Proof.Poly1305.X86.After st s s₁ g rs) (hc : VG.Proof.Poly1305.X86.Ctx st s) (he : Reg.edi ∉ rs := by decide) : VG.Proof.Poly1305.X86.Ctx st s₁ :=
  hc.keep (h.gpr _ he) h.wr

theorem trans (h₁ : VG.Proof.Poly1305.X86.After st s s₁ g₁ rs₁) (h₂ : VG.Proof.Poly1305.X86.After st s₁ s₂ g₂ rs₂) : VG.Proof.Poly1305.X86.After st s s₂ g₂ (rs₁ ++ rs₂) :=
  ⟨h₂.words, h₁.frame.trans h₂.frame, fun r hr => by
    rw [List.mem_append, not_or] at hr; rw [h₂.gpr r hr.2, h₁.gpr r hr.1], h₂.rd.trans h₁.rd,
    h₂.wr.trans h₁.wr⟩

theorem mono {rs' : List Reg} (h : VG.Proof.Poly1305.X86.After st s s₁ g rs) (hs : ∀ r ∈ rs, r ∈ rs' := by decide) : VG.Proof.Poly1305.X86.After st s s₁ g rs' :=
  ⟨h.words, h.frame, fun r hr => h.gpr r fun h' => hr (hs r h'), h.rd, h.wr⟩

/-- A word of a region disjoint from the state, unchanged. -/
theorem wd (h : VG.Proof.Poly1305.X86.After st s s₁ g rs) {x : BitVec 32} {d : Nat} (hd : (VG.Proof.Poly1305.X86.sub x d 4).Disjoint (VG.Proof.Poly1305.X86.sR st)) :
    X86.wd s₁.mem x d = X86.wd s.mem x d :=
  VG.Proof.Poly1305.X86.wd_frame h.frame (by simpa using hd)

end After

/-- `mov eax, [edi + 4 j]; op eax, src; mov [edi + 4 j'], eax` with `op` an
addition of the source's value `x` and the carry `cin`: the sum is stored, and
CF is its carry out. -/
theorem los_ok {st : BitVec 32} {s : State} (hc : VG.Proof.Poly1305.X86.Ctx st s) {f : Nat → Nat} (hw : VG.Proof.Poly1305.X86.Words s.mem st f)
    {a b j j' : Nat} (ha : a = 4 * j) (hb : b = 4 * j') (hj : j < 32) (hj' : j' < 32)
    {op : AluOp} {src : Src} {cin : Bool} {x : BitVec 32}
    (hop : (op = .add ∧ cin = false) ∨ (op = .adc ∧ s.cf = some cin))
    (hsrc : ∀ s' y, VG.Proof.Poly1305.X86.Upd s s' .eax y → readSrc s' src = some x) :
    WP isa (.block [.mov .eax (.mem (at_ .edi a)), .alu op .eax src, .store (at_ .edi b) .eax]) s
      fun s' => VG.Proof.Poly1305.X86.After st s s' (VG.Proof.Poly1305.X86.upd f j' ((f j + x.toNat + cin.toNat) % 2 ^ 32)) [.eax] ∧
        s'.cf = some (decide (2 ^ 32 ≤ f j + x.toNat + cin.toNat)) := by
  subst ha hb
  have hfit := hc.fit
  refine VG.Proof.Poly1305.X86.wp_movm (a := addr st (4 * j)) (by rw [VG.Proof.Poly1305.X86.ea_at, hc.edi]) (hc.inRW (by omega_using [hj]) (by decide))
    fun s₁ u₁ cf₁ => ?_
  have hx := hsrc s₁ _ u₁
  have e₁ : (s₁.gpr .eax).toNat = f j := by rw [u₁.gpr]; exact hw j hj
  -- The last step, for both operations.
  have fin : ∀ (s₂ : State) (y : BitVec 32), VG.Proof.Poly1305.X86.Upd s₁ s₂ .eax y → y.toNat = (f j + x.toNat + cin.toNat) % 2 ^ 32 →
      s₂.cf = some (decide (2 ^ 32 ≤ f j + x.toNat + cin.toNat)) →
      WP isa (.block [.store (at_ .edi (4 * j')) .eax]) s₂ fun s' =>
        VG.Proof.Poly1305.X86.After st s s' (VG.Proof.Poly1305.X86.upd f j' ((f j + x.toNat + cin.toNat) % 2 ^ 32)) [.eax] ∧
        s'.cf = some (decide (2 ^ 32 ≤ f j + x.toNat + cin.toNat)) := by
    intro s₂ y u₂ hy cf₂
    have edi₂ : s₂.gpr .edi = st := by rw [u₂.other _ (by decide), u₁.other _ (by decide), hc.edi]
    refine VG.Proof.Poly1305.X86.wp_store (a := addr st (4 * j')) (by rw [VG.Proof.Poly1305.X86.ea_at, edi₂])
      (by rw [u₂.wr, u₁.wr]; exact hc.inW (by omega_using [hj']) (by decide)) fun s₃ u₃ => WP.block_nil ?_
    rw [u₂.gpr] at u₃
    refine ⟨⟨?_, ?_, fun r hr => ?_, by rw [u₃.rd, u₂.rd, u₁.rd], by rw [u₃.wr, u₂.wr, u₁.wr]⟩,
      by rw [u₃.cf]; exact cf₂⟩
    · rw [u₃.mem, u₂.mem, u₁.mem, ← hy]; exact hw.write hfit hj' y
    · rw [u₃.mem, u₂.mem, u₁.mem]; exact VG.Proof.Poly1305.X86.frame_write (Frame.refl _ _) hfit (by omega_using [hj']) y
    · simp only [List.mem_singleton] at hr
      rw [u₃.gpr, u₂.other r hr, u₁.other r hr]
  rcases hop with ⟨rfl, rfl⟩ | ⟨rfl, hcf⟩
  · refine VG.Proof.Poly1305.X86.wp_addx hx fun s₂ u₂ cf₂ => fin s₂ _ u₂ ?_ (by rw [cf₂, e₁]; rfl)
    rw [BitVec.toNat_add, e₁]; rfl
  · refine VG.Proof.Poly1305.X86.wp_adcx hx (by rw [cf₁]; exact hcf) fun s₂ u₂ cf₂ => fin s₂ _ u₂ ?_ (by rw [cf₂, e₁])
    rw [VG.Proof.Poly1305.X86.add3_toNat, e₁]


/-! ## Adding a block -/

/-- A word of the block at `b + d` as a source, in any state that differs only in `eax`. -/
theorem src_blk {s : State} {b : Reg} (hb : b ≠ .eax) {d : Nat} {a : Addr} (hea : addr (s.gpr b) d = a)
    (hin : InRegions (s.rd ++ s.wr) a 4) :
    ∀ s' y, VG.Proof.Poly1305.X86.Upd s s' .eax y → readSrc s' (.mem (at_ b d)) = some (s.mem.readW a 32) := by
  intro s' y u
  rw [VG.Proof.Poly1305.X86.readSrc_mem (a := a) (by rw [VG.Proof.Poly1305.X86.ea_at, u.other _ hb, hea]) (by rw [u.rd, u.wr]; exact hin), u.mem]

theorem src_imm {s : State} (w : BitVec 32) :
    ∀ s' y, VG.Proof.Poly1305.X86.Upd s s' .eax y → readSrc s' (.imm w) = some w := fun _ _ _ => rfl

/-- Word `i` of the block at `b + d` (word `i` at `bp`) added to word `i` of
`h`, with the carry in unless `i = 0`. -/
theorem addWord_ok {st bp : BitVec 32} {s : State} (hc : VG.Proof.Poly1305.X86.Ctx st s) {f : Nat → Nat}
    (hw : VG.Proof.Poly1305.X86.Words s.mem st f) {b : Reg} (hb : b ≠ .eax) {d i : Nat} (hi : i < 4)
    (hea : addr (s.gpr b) (d + 4 * i) = addr bp (4 * i)) {cin : Bool}
    (hop : (i = 0 ∧ cin = false) ∨ (i ≠ 0 ∧ s.cf = some cin))
    (hin : InRegions (s.rd ++ s.wr) (addr bp (4 * i)) 4) :
    WP isa (.block (addWord b d i)) s fun s' =>
      VG.Proof.Poly1305.X86.After st s s' (VG.Proof.Poly1305.X86.upd f i ((f i + VG.Proof.Poly1305.X86.wv s.mem bp (4 * i) + cin.toNat) % 2 ^ 32)) [.eax] ∧
      s'.cf = some (decide (2 ^ 32 ≤ f i + VG.Proof.Poly1305.X86.wv s.mem bp (4 * i) + cin.toNat)) :=
  VG.Proof.Poly1305.X86.los_ok hc hw rfl rfl (by omega_using [hi]) (by omega_using [hi])
    (by rcases hop with ⟨rfl, rfl⟩ | ⟨h, h'⟩
        · exact .inl ⟨rfl, rfl⟩
        · exact .inr ⟨by simp only [h, ↓reduceIte], h'⟩)
    (VG.Proof.Poly1305.X86.src_blk hb hea hin)

end VG.Proof.Poly1305.X86

end

-- Formerly the module `VerifiedGarbage.Proof.Poly1305.X86.Reduce`.
section

section

/-!
# Poly1305 on x86 (32-bit): absorbing a block
-/

namespace VG.Proof.Poly1305.X86

open VG VG.X86 VG.Impl.Poly1305.X86
open VG.Spec.Poly1305 (P)

theorem carry_dec {x : Nat} (h : x < 2 ^ 33) : (decide (2 ^ 32 ≤ x)).toNat = x / 2 ^ 32 := by
  by_cases h' : 2 ^ 32 ≤ x
  · rw [decide_eq_true h', Bool.toNat_true]; omega_using [h, h']
  · rw [decide_eq_false h', Bool.toNat_false]; omega_using [h, h']

/-! ## `h += m + pad · 2¹²⁸` -/

section
variable (f : Nat → Nat) (b : Nat → Nat) (pad : Nat)
/-- The sums of the words of `h` and of the block, with the carries. -/
def asum : Nat → Nat
  | 0 => f 0 + b 0
  | k + 1 => f (k + 1) + (if k + 1 = 4 then pad else b (k + 1)) + VG.Proof.Poly1305.X86.asum k / 2 ^ 32
end

theorem addBlock_eq (b : Reg) (d : Nat) (pad : BitVec 32) : addBlock b d pad = addWord b d 0 ++
    (addWord b d 1 ++ (addWord b d 2 ++
    (addWord b d 3 ++ ([.mov .eax (.mem (at_ .edi (hOff 4))), .alu .adc .eax (.imm pad),
      .store (at_ .edi (hOff 4)) .eax] : List Instr)))) := by
  simp only [addBlock, List.append_assoc]

theorem asum_lt {f b : Nat → Nat} {pad : Nat} (hf : ∀ k < 5, f k < 2 ^ 32) (hb : ∀ k < 4, b k < 2 ^ 32)
    (hp : pad < 2 ^ 32) : ∀ k < 5, VG.Proof.Poly1305.X86.asum f b pad k < 2 ^ 33 := by
  intro k hk
  induction k with
  | zero => have := hf 0 (by decide); have := hb 0 (by decide); simp only [VG.Proof.Poly1305.X86.asum]; omega
  | succ k ih =>
    have := ih (by omega_using [hk]); have := hf (k + 1) hk
    simp only [VG.Proof.Poly1305.X86.asum]
    split
    · omega
    · have := hb (k + 1) (by omega); omega


theorem Words.congr {m : Mem} {st : BitVec 32} {g g' : Nat → Nat} (h : VG.Proof.Poly1305.X86.Words m st g)
    (he : ∀ k < 32, g k = g' k) : VG.Proof.Poly1305.X86.Words m st g' := fun k hk => (h k hk).trans (he k hk)

theorem After.congr {st : BitVec 32} {s s' : State} {g g' : Nat → Nat} {rs : List Reg}
    (h : VG.Proof.Poly1305.X86.After st s s' g rs) (he : ∀ k < 32, g k = g' k) : VG.Proof.Poly1305.X86.After st s s' g' rs :=
  ⟨h.words.congr he, h.frame, h.gpr, h.rd, h.wr⟩

section
variable (st bp : BitVec 32) (s : State) (f : Nat → Nat) (pad : BitVec 32)

/-- The block's words, as numbers. -/
abbrev bw (k : Nat) : Nat := VG.Proof.Poly1305.X86.wv s.mem bp (4 * k)

/-- After `addWord` for the words below `i`. -/
def AddInv (i : Nat) (s' : State) : Prop :=
  VG.Proof.Poly1305.X86.After st s s' (fun k => if k < i then VG.Proof.Poly1305.X86.asum f (VG.Proof.Poly1305.X86.bw bp s) pad.toNat k % 2 ^ 32 else f k) [.eax] ∧
    s'.cf = some (decide (2 ^ 32 ≤ VG.Proof.Poly1305.X86.asum f (VG.Proof.Poly1305.X86.bw bp s) pad.toNat (i - 1)))
end

/-- The hypotheses of `addBlock_ok`: the block at `b + d` is at `bp`, outside
the state or in its buffer (words 14 to 17). -/
structure AddPre (st bp : BitVec 32) (b : Reg) (d : Nat) (s : State) (f : Nat → Nat) : Prop where
  ctx : VG.Proof.Poly1305.X86.Ctx st s
  words : VG.Proof.Poly1305.X86.Words s.mem st f
  base : b ≠ .eax
  ea : ∀ k < 4, addr (s.gpr b) (d + 4 * k) = addr bp (4 * k)
  rd : ∀ k < 4, InRegions (s.rd ++ s.wr) (addr bp (4 * k)) 4
  disj : ∀ k < 4, (VG.Proof.Poly1305.X86.sub bp (4 * k) 4).Disjoint (VG.Proof.Poly1305.X86.sR st) ∨ addr bp (4 * k) = addr st (4 * (14 + k))

theorem addFirst_ok {st bp : BitVec 32} {b : Reg} {d : Nat} {s : State} {f : Nat → Nat}
    (hp : VG.Proof.Poly1305.X86.AddPre st bp b d s f) (pad : BitVec 32) :
    WP isa (.block (addWord b d 0)) s (VG.Proof.Poly1305.X86.AddInv st bp s f pad 1) := by
  refine WP.mono (VG.Proof.Poly1305.X86.addWord_ok hp.ctx hp.words hp.base (i := 0) (by decide) (hp.ea 0 (by decide))
    (.inl ⟨rfl, rfl⟩) (hp.rd 0 (by decide))) fun s₁ ⟨A₁, c₁⟩ => ⟨A₁.congr fun k _ => ?_, by rw [c₁]; rfl⟩
  by_cases e : k = 0
  · subst e; simp only [VG.Proof.Poly1305.X86.upd, ↓reduceIte, Nat.mul_zero, Bool.toNat_false, Nat.add_zero, Nat.reducePow, Nat.lt_add_one, VG.Proof.Poly1305.X86.asum, VG.Proof.Poly1305.X86.bw]
  · simp only [VG.Proof.Poly1305.X86.upd, e, ↓reduceIte, Nat.lt_one_iff]

theorem addStep_ok {st bp : BitVec 32} {b : Reg} {d : Nat} {s : State} {f : Nat → Nat}
    (hp : VG.Proof.Poly1305.X86.AddPre st bp b d s f) (pad : BitVec 32) {i : Nat} (hi : 1 ≤ i ∧ i < 4) {s' : State}
    (h : VG.Proof.Poly1305.X86.AddInv st bp s f pad i s') :
    WP isa (.block (addWord b d i)) s' (VG.Proof.Poly1305.X86.AddInv st bp s f pad (i + 1)) := by
  obtain ⟨A, c⟩ := h
  have hb : VG.Proof.Poly1305.X86.bw bp s' i = VG.Proof.Poly1305.X86.bw bp s i := by
    rcases hp.disj i (by omega_using [hi]) with hd | he
    · simp only [VG.Proof.Poly1305.X86.bw, VG.Proof.Poly1305.X86.wv]; rw [A.wd hd]
    · simp only [VG.Proof.Poly1305.X86.bw, VG.Proof.Poly1305.X86.wv, VG.Proof.Poly1305.X86.wd]
      rw [he, show (s'.mem.readW (addr st (4 * (14 + i))) 32).toNat = _ from A.words (14 + i) (by omega_using [hi]),
        show (s.mem.readW (addr st (4 * (14 + i))) 32).toNat = _ from hp.words (14 + i) (by omega_using [hi]),
        ite_eq_right (by omega_using [])]
  have hlt := VG.Proof.Poly1305.X86.asum_lt (f := f) (b := VG.Proof.Poly1305.X86.bw bp s) (pad := pad.toNat) (fun k hk => hp.words.lt (by omega_using [hk]))
    (fun k _ => BitVec.isLt _) pad.isLt
  refine WP.mono (VG.Proof.Poly1305.X86.addWord_ok (bp := bp) (A.ctx hp.ctx) A.words hp.base (i := i) (by omega_using [hi])
    (by rw [A.gpr _ (by simpa using hp.base)]; exact hp.ea i (by omega_using [hi])) (.inr ⟨by omega_using [hi], c⟩)
    (by rw [A.rd, A.wr]; exact hp.rd i (by omega_using [hi])))
    fun s₁ ⟨A₁, c₁⟩ => ⟨(A.trans A₁).mono (rs' := [.eax]) |>.congr fun k _ => ?_, ?_⟩
  · rw [show VG.Proof.Poly1305.X86.bw bp s' i = VG.Proof.Poly1305.X86.wv s'.mem bp (4 * i) from rfl] at hb
    by_cases e : k = i
    · subst e
      simp only [VG.Proof.Poly1305.X86.upd, ite_true, show ¬ k < k by omega_using [], ite_false, show k < k + 1 by omega_using []]
      rw [hb, VG.Proof.Poly1305.X86.carry_dec (hlt (k - 1) (by omega_using [hi]))]
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega_using [hi]⟩
      simp only [VG.Proof.Poly1305.X86.asum, show j + 1 ≠ 4 by omega_using [hi], ite_false, Nat.add_sub_cancel]
    · simp only [VG.Proof.Poly1305.X86.upd, e, ite_false]
      by_cases e' : k < i
      · simp only [e', ↓reduceIte, Nat.reducePow, show k < i + 1 by omega_using [e']]
      · simp only [e', ↓reduceIte, show ¬k < i + 1 by omega_using [e, e']]
  · rw [c₁]
    simp only [show i + 1 - 1 = i by omega_using [hi], show ¬ i < i by omega_using [], ite_false]
    rw [show VG.Proof.Poly1305.X86.wv s'.mem bp (4 * i) = VG.Proof.Poly1305.X86.bw bp s i from hb, VG.Proof.Poly1305.X86.carry_dec (hlt (i - 1) (by omega_using [hi]))]
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega_using [hi]⟩
    simp only [VG.Proof.Poly1305.X86.asum, show j + 1 ≠ 4 by omega_using [hi], ite_false, Nat.add_sub_cancel]

/-- `h += m + pad · 2¹²⁸` for the block `m` at `b + d`: the words `asum mod 2³²`. -/
theorem addBlock_ok {st bp : BitVec 32} {b : Reg} {d : Nat} {s : State} {f : Nat → Nat}
    (hp : VG.Proof.Poly1305.X86.AddPre st bp b d s f) (pad : BitVec 32) :
    WP isa (.block (addBlock b d pad)) s fun s' =>
      VG.Proof.Poly1305.X86.After st s s' (fun k => if k < 5 then VG.Proof.Poly1305.X86.asum f (VG.Proof.Poly1305.X86.bw bp s) pad.toNat k % 2 ^ 32 else f k) [.eax] := by
  have hlt := VG.Proof.Poly1305.X86.asum_lt (f := f) (b := VG.Proof.Poly1305.X86.bw bp s) (pad := pad.toNat) (fun k hk => hp.words.lt (by omega_using [hk]))
    (fun k _ => BitVec.isLt _) pad.isLt
  rw [VG.Proof.Poly1305.X86.addBlock_eq]
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86.addFirst_ok hp pad) fun s₁ h₁ => ?_)
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86.addStep_ok hp pad (i := 1) (by decide) h₁) fun s₂ h₂ => ?_)
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86.addStep_ok hp pad (i := 2) (by decide) h₂) fun s₃ h₃ => ?_)
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86.addStep_ok hp pad (i := 3) (by decide) h₃) fun s₄ ⟨A, c⟩ => ?_)
  refine WP.mono (VG.Proof.Poly1305.X86.los_ok (A.ctx hp.ctx) A.words (j := 4) (j' := 4) rfl rfl (by decide) (by decide)
    (.inr ⟨rfl, c⟩) (VG.Proof.Poly1305.X86.src_imm pad)) fun s₅ ⟨A₅, _⟩ => (A.trans A₅).mono (rs' := [.eax]) |>.congr fun k _ => ?_
  by_cases e : k = 4
  · subst e
    simp only [VG.Proof.Poly1305.X86.upd, ite_true, show ¬ (4 : Nat) < 4 by decide, ite_false, show (4 : Nat) < 5 by decide]
    rw [VG.Proof.Poly1305.X86.carry_dec (hlt 3 (by decide))]
    simp only [VG.Proof.Poly1305.X86.asum, ite_true, show (3 : Nat) + 1 = 4 from rfl]
  · simp only [VG.Proof.Poly1305.X86.upd, e, ite_false]
    by_cases e' : k < 4
    · simp only [Nat.reduceAdd, e', ↓reduceIte, Nat.reducePow, show k < 5 by omega_using [e']]
    · simp only [Nat.reduceAdd, e', ↓reduceIte, show ¬k < 5 by omega_using [e, e']]


/-! ## The sums of products -/

/-- The word index of the coefficient of `hi` in `dk` (`coef k i = 4 * cidx k i`). -/
def cidx (k i : Nat) : Nat := if i ≤ k then 18 + (k - i) else 21 + (k + 4 - i)

theorem coef_eq (k i : Nat) : coef k i = 4 * VG.Proof.Poly1305.X86.cidx k i := by
  simp only [coef, VG.Proof.Poly1305.X86.cidx, rOff, sOff]; split <;> omega_using []

theorem cidx_lt : ∀ k < 4, ∀ i < 5, VG.Proof.Poly1305.X86.cidx k i < 32 ∧ 18 ≤ VG.Proof.Poly1305.X86.cidx k i ∧ VG.Proof.Poly1305.X86.cidx k i < 25 := by decide +kernel

section
variable (g : Nat → Nat)
/-- `dk`'s sum of products, from the words `g`. -/
def dterm (k : Nat) : Nat := ((List.range (nterms k)).map fun i => g i * g (VG.Proof.Poly1305.X86.cidx k i)).sum

/-- `dk`, with the carries from `d(k-1)`. -/
def dv : Nat → Nat
  | 0 => VG.Proof.Poly1305.X86.dterm g 0
  | k + 1 => VG.Proof.Poly1305.X86.dv k / 2 ^ 32 + VG.Proof.Poly1305.X86.dterm g (k + 1)
end

theorem dsum_eq (k : Nat) : dsum k = (((List.range (nterms k)).map fun i => (i, coef k i)).flatMap
    fun p => mac p.1 p.2) ++ ([.store (at_ .edi (tOff k)) .ebx, .mov .ebx (.reg .ebp), .mov .ebp (.imm 0)] : List Instr) := by
  rw [dsum, List.flatMap_map]

/-- `dk`, from the accumulator `A` in `ebx:ebp`: its low word stored, and its
high word as the new accumulator. -/
theorem dsum_ok {st : BitVec 32} {s : State} (hc : VG.Proof.Poly1305.X86.Ctx st s) {g : Nat → Nat} (hw : VG.Proof.Poly1305.X86.Words s.mem st g)
    {k : Nat} (hk : k < 4) (hb : VG.Proof.Poly1305.X86.acc s + VG.Proof.Poly1305.X86.dterm g k < 2 ^ 64) :
    WP isa (.block (dsum k)) s fun s' =>
      VG.Proof.Poly1305.X86.After st s s' (VG.Proof.Poly1305.X86.upd g (25 + k) ((VG.Proof.Poly1305.X86.acc s + VG.Proof.Poly1305.X86.dterm g k) % 2 ^ 32)) [.eax, .ecx, .edx, .ebx, .ebp] ∧
      VG.Proof.Poly1305.X86.acc s' = (VG.Proof.Poly1305.X86.acc s + VG.Proof.Poly1305.X86.dterm g k) / 2 ^ 32 := by
  have hfit := hc.fit
  rw [VG.Proof.Poly1305.X86.dsum_eq]
  have hL : ∀ p ∈ ((List.range (nterms k)).map fun i => (i, coef k i)),
      InRegions (s.rd ++ s.wr) (addr (s.gpr .edi) (hOff p.1)) 4 ∧
      InRegions (s.rd ++ s.wr) (addr (s.gpr .edi) p.2) 4 := by
    intro p hp
    simp only [List.mem_map, List.mem_range] at hp
    obtain ⟨i, hi, rfl⟩ := hp
    have hn : nterms k ≤ 5 := by simp only [nterms]; split <;> omega_using []
    obtain ⟨-, -, h3⟩ := VG.Proof.Poly1305.X86.cidx_lt k hk i (by omega_using [hi, hn])
    exact ⟨hc.inRW' (by simp only [hOff]; omega_using [hi, hn]), hc.inRW' (by rw [VG.Proof.Poly1305.X86.coef_eq]; omega_using [h3])⟩
  have hsum : (((List.range (nterms k)).map fun i => (i, coef k i)).map fun p =>
      VG.Proof.Poly1305.X86.wv s.mem (s.gpr .edi) (hOff p.1) * VG.Proof.Poly1305.X86.wv s.mem (s.gpr .edi) p.2).sum = VG.Proof.Poly1305.X86.dterm g k := by
    rw [List.map_map, VG.Proof.Poly1305.X86.dterm]
    congr 1
    refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    have hn : nterms k ≤ 5 := by simp only [nterms]; split <;> omega_using []
    obtain ⟨h1, -, -⟩ := VG.Proof.Poly1305.X86.cidx_lt k hk i (by omega_using [hi, hn])
    simp only [Function.comp_apply, hc.edi, hOff, VG.Proof.Poly1305.X86.coef_eq]
    rw [hw i (by omega_using [hi, hn]), hw _ h1]
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86.macs_ok _ s hL) fun s₁ ⟨e₁, k₁⟩ => ?_)
  rw [hsum] at e₁
  have e₁ := e₁ hb
  have edi₁ : s₁.gpr .edi = st := by rw [k₁.gpr', hc.edi]
  have hebp : VG.Proof.Poly1305.X86.v s₁ .ebp = (VG.Proof.Poly1305.X86.acc s + VG.Proof.Poly1305.X86.dterm g k) / 2 ^ 32 := by
    have := (s₁.gpr .ebx).isLt; simp only [VG.Proof.Poly1305.X86.acc, VG.Proof.Poly1305.X86.v] at e₁ ⊢; omega_using [hsum, e₁]
  have hebx : VG.Proof.Poly1305.X86.v s₁ .ebx = (VG.Proof.Poly1305.X86.acc s + VG.Proof.Poly1305.X86.dterm g k) % 2 ^ 32 := by
    have := (s₁.gpr .ebx).isLt; simp only [VG.Proof.Poly1305.X86.acc, VG.Proof.Poly1305.X86.v] at e₁ ⊢; omega_using [hsum, e₁]
  refine VG.Proof.Poly1305.X86.wp_store (a := addr st (tOff k)) (by rw [VG.Proof.Poly1305.X86.ea_at, edi₁])
    (by rw [k₁.2.2.2]; exact hc.inW (by simp only [tOff]; omega_using [hk]) (by decide)) fun s₂ u₂ => ?_
  refine VG.Proof.Poly1305.X86.wp_mov fun s₃ u₃ _ => VG.Proof.Poly1305.X86.wp_movi fun s₄ u₄ _ => WP.block_nil ⟨⟨?_, ?_, fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · rw [u₄.mem, u₃.mem, u₂.mem, k₁.2.1, show tOff k = 4 * (25 + k) by simp only [tOff]; omega_using []]
    rw [← hebx]
    exact hw.write hfit (by omega_using [hk]) _
  · rw [u₄.mem, u₃.mem, u₂.mem, k₁.2.1]
    exact VG.Proof.Poly1305.X86.frame_write (Frame.refl _ _) hfit (by simp only [tOff]; omega_using [hk]) _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₄.other r hr.2.2.2.2, u₃.other r hr.2.2.2.1, u₂.gpr, k₁.1 r (by simp only [List.mem_cons, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, List.not_mem_nil, or_self, not_false_eq_true])]
  · rw [u₄.rd, u₃.rd, u₂.rd, k₁.2.2.1]
  · rw [u₄.wr, u₃.wr, u₂.wr, k₁.2.2.2]
  · simp only [VG.Proof.Poly1305.X86.acc, VG.Proof.Poly1305.X86.v]
    rw [u₄.gpr, u₄.other _ (by decide), u₃.gpr, u₂.gpr]
    have : (0 : BitVec 32).toNat = 0 := rfl
    rw [this, ← hebp]
    simp only [VG.Proof.Poly1305.X86.v]; omega_using []


theorem dterm_congr {g g' : Nat → Nat} (h : ∀ i < 25, g i = g' i) {k : Nat} (hk : k < 4) :
    VG.Proof.Poly1305.X86.dterm g k = VG.Proof.Poly1305.X86.dterm g' k := by
  simp only [VG.Proof.Poly1305.X86.dterm]
  congr 1
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  have hn : nterms k ≤ 5 := by simp only [nterms]; split <;> omega_using []
  obtain ⟨-, -, h3⟩ := VG.Proof.Poly1305.X86.cidx_lt k hk i (by omega_using [hi, hn])
  rw [h i (by omega_using [hi, hn]), h _ h3]

/-- The words after `n` of the sums of products: `tk = dk mod 2³²`. -/
def dwords (g : Nat → Nat) (n : Nat) : Nat → Nat :=
  fun k => if 25 ≤ k ∧ k < 25 + n then VG.Proof.Poly1305.X86.dv g (k - 25) % 2 ^ 32 else g k

theorem dsums_ok {st : BitVec 32} {s : State} (hc : VG.Proof.Poly1305.X86.Ctx st s) {g : Nat → Nat} (hw : VG.Proof.Poly1305.X86.Words s.mem st g)
    (hacc : VG.Proof.Poly1305.X86.acc s = 0) (hb : ∀ k < 4, VG.Proof.Poly1305.X86.dv g k < 2 ^ 64) :
    ∀ n ≤ 4, WP isa (.block ((List.range n).flatMap dsum)) s fun s' =>
      VG.Proof.Poly1305.X86.After st s s' (VG.Proof.Poly1305.X86.dwords g n) [.eax, .ecx, .edx, .ebx, .ebp] ∧
      VG.Proof.Poly1305.X86.acc s' = if n = 0 then 0 else VG.Proof.Poly1305.X86.dv g (n - 1) / 2 ^ 32 := by
  intro n hn
  induction n with
  | zero =>
    refine WP.block_nil ⟨⟨hw.congr fun k _ => ?_, Frame.refl _ _, fun _ _ => rfl, rfl, rfl⟩, hacc⟩
    simp only [VG.Proof.Poly1305.X86.dwords]; split <;> omega
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (ih (by omega_using [hn])) fun s₁ ⟨A₁, e₁⟩ => ?_)
    have hd : VG.Proof.Poly1305.X86.dterm (VG.Proof.Poly1305.X86.dwords g n) n = VG.Proof.Poly1305.X86.dterm g n :=
      VG.Proof.Poly1305.X86.dterm_congr (fun i hi => by simp only [VG.Proof.Poly1305.X86.dwords]; rw [ite_eq_right (by omega_using [hi])]) (by omega_using [hn])
    have hv : VG.Proof.Poly1305.X86.acc s₁ + VG.Proof.Poly1305.X86.dterm (VG.Proof.Poly1305.X86.dwords g n) n = VG.Proof.Poly1305.X86.dv g n := by
      rw [hd, e₁]
      cases n with
      | zero => simp only [↓reduceIte, Nat.zero_add, VG.Proof.Poly1305.X86.dv]
      | succ n => simp [VG.Proof.Poly1305.X86.dv]
    refine WP.mono (VG.Proof.Poly1305.X86.dsum_ok (A₁.ctx hc) A₁.words (k := n) (by omega_using [hn]) (by rw [hv]; exact hb n (by omega_using [hn])))
      fun s₂ ⟨A₂, e₂⟩ => ⟨(A₁.trans A₂).mono.congr fun k _ => ?_, by rw [e₂, hv]; simp only [Nat.reducePow, Nat.add_eq_zero_iff, Nat.succ_ne_self, and_false, ↓reduceIte, Nat.add_one_sub_one]⟩
    rw [hv]
    simp only [VG.Proof.Poly1305.X86.upd, VG.Proof.Poly1305.X86.dwords]
    by_cases e : k = 25 + n
    · subst e; simp
    · rw [ite_eq_right e]
      by_cases e' : 25 ≤ k ∧ k < 25 + n
      · rw [ite_eq_left e', ite_eq_left ⟨e'.1, by omega_using [e']⟩]
      · rw [ite_eq_right e', ite_eq_right (by omega_using [e, e'])]

theorem products_eq : products = .mov .ebx (.imm 0) :: .mov .ebp (.imm 0) ::
    ((List.range 4).flatMap dsum ++ mac 4 (rOff 0)) := by
  simp only [products, List.cons_append, List.nil_append]

/-- The sums of products: `t0, …, t3` stored, and `d4` in `ebx`. -/
theorem products_ok {st : BitVec 32} {s : State} (hc : VG.Proof.Poly1305.X86.Ctx st s) {g : Nat → Nat} (hw : VG.Proof.Poly1305.X86.Words s.mem st g)
    (hb : ∀ k < 4, VG.Proof.Poly1305.X86.dv g k < 2 ^ 64) (h4 : VG.Proof.Poly1305.X86.dv g 3 / 2 ^ 32 + g 4 * g 18 < 2 ^ 32) :
    WP isa (.block products) s fun s' =>
      VG.Proof.Poly1305.X86.After st s s' (VG.Proof.Poly1305.X86.dwords g 4) [.eax, .ecx, .edx, .ebx, .ebp] ∧
      VG.Proof.Poly1305.X86.v s' .ebx = VG.Proof.Poly1305.X86.dv g 3 / 2 ^ 32 + g 4 * g 18 := by
  rw [VG.Proof.Poly1305.X86.products_eq]
  refine VG.Proof.Poly1305.X86.wp_movi fun s₁ u₁ _ => VG.Proof.Poly1305.X86.wp_movi fun s₂ u₂ _ => ?_
  have A₂ : VG.Proof.Poly1305.X86.After st s s₂ g [.eax, .ecx, .edx, .ebx, .ebp] :=
    ⟨by rw [u₂.mem, u₁.mem]; exact hw, by rw [u₂.mem, u₁.mem]; exact Frame.refl _ _, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [u₂.other r hr.2.2.2.2, u₁.other r hr.2.2.2.1], by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr]⟩
  have hacc : VG.Proof.Poly1305.X86.acc s₂ = 0 := by
    simp only [VG.Proof.Poly1305.X86.acc, VG.Proof.Poly1305.X86.v]; rw [u₂.gpr, u₂.other _ (by decide), u₁.gpr]; rfl
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86.dsums_ok (A₂.ctx hc) A₂.words hacc hb 4 (Nat.le_refl _))
    fun s₃ ⟨A₃, e₃⟩ => ?_)
  have c₃ := (A₂.trans A₃).ctx hc
  refine WP.mono (VG.Proof.Poly1305.X86.mac_ok s₃ 4 (rOff 0) (c₃.inRW' (by simp only [hOff, Nat.reduceMul, Nat.reduceAdd, Nat.reduceLeDiff])) (c₃.inRW' (by simp only [rOff, Nat.mul_zero, Nat.add_zero, Nat.reduceAdd, Nat.reduceLeDiff])))
    fun s₄ ⟨e₄, k₄⟩ => ⟨?_, ?_⟩
  · exact ⟨k₄.2.1 ▸ A₃.words, A₂.frame.trans (k₄.2.1 ▸ A₃.frame), fun r hr => by
      rw [k₄.1 r hr, A₃.gpr r hr, A₂.gpr r hr], by rw [k₄.2.2.1, A₃.rd, A₂.rd],
      by rw [k₄.2.2.2, A₃.wr, A₂.wr]⟩
  · have w4 : VG.Proof.Poly1305.X86.wv s₃.mem (s₃.gpr .edi) (hOff 4) = g 4 := by
      rw [c₃.edi, show hOff 4 = 4 * 4 from rfl, A₃.words 4 (by decide)]; simp only [VG.Proof.Poly1305.X86.dwords, Nat.reduceLeDiff, Nat.reduceAdd, Nat.reduceLT, and_true, ↓reduceIte]
    have w14 : VG.Proof.Poly1305.X86.wv s₃.mem (s₃.gpr .edi) (rOff 0) = g 18 := by
      rw [c₃.edi, show rOff 0 = 4 * 18 from rfl, A₃.words 18 (by decide)]; simp only [VG.Proof.Poly1305.X86.dwords, Nat.reduceLeDiff, Nat.reduceAdd, Nat.reduceLT, and_true, ↓reduceIte]
    rw [w4, w14, show VG.Proof.Poly1305.X86.acc s₃ = VG.Proof.Poly1305.X86.dv g 3 / 2 ^ 32 by rw [e₃]; rfl] at e₄
    have e₄ := e₄ (by omega_using [h4])
    simp only [VG.Proof.Poly1305.X86.acc, VG.Proof.Poly1305.X86.v] at e₄ ⊢
    omega_using [h4, e₄]


/-! ## The carry -/

section
variable (G : Nat → Nat) (d4 : Nat)
/-- The sums of `5 ⌊d4 / 4⌋ + t` and `2¹²⁸ (d4 mod 4)`, with the carries. -/
def csum : Nat → Nat
  | 0 => 5 * (d4 / 4) + G 25
  | k + 1 => (if k + 1 = 4 then d4 % 4 else G (25 + (k + 1))) + VG.Proof.Poly1305.X86.csum k / 2 ^ 32
end

theorem csum_lt {G : Nat → Nat} {d4 : Nat} (hG : ∀ k < 4, G (25 + k) < 2 ^ 32)
    (he : 5 * (d4 / 4) < 2 ^ 32) : ∀ k < 5, VG.Proof.Poly1305.X86.csum G d4 k < 2 ^ 33 := by
  intro k hk
  induction k with
  | zero => have := hG 0 (by decide); simp only [Nat.add_zero] at this; simp only [VG.Proof.Poly1305.X86.csum]; omega_using [he, this]
  | succ k ih =>
    have := ih (by omega_using [hk])
    simp only [VG.Proof.Poly1305.X86.csum]
    split
    · omega_using [this]
    · have := hG (k + 1) (by omega); omega

theorem carry_eq : VG.Impl.Poly1305.X86.carry =
    ([.mov .eax (.reg .ebx), .shift .shr .eax 2, .mov .ecx (.reg .eax), .alu .add .eax (.reg .eax),
      .alu .add .eax (.reg .eax), .alu .add .eax (.reg .ecx), .alu .and .ebx (.imm 3),
      .alu .add .eax (.mem (at_ .edi (tOff 0))), .store (at_ .edi (hOff 0)) .eax] : List Instr) ++
    (([.mov .eax (.mem (at_ .edi (tOff 1))), .alu .adc .eax (.imm 0), .store (at_ .edi (hOff 1)) .eax] : List Instr) ++
    (([.mov .eax (.mem (at_ .edi (tOff 2))), .alu .adc .eax (.imm 0), .store (at_ .edi (hOff 2)) .eax] : List Instr) ++
    (([.mov .eax (.mem (at_ .edi (tOff 3))), .alu .adc .eax (.imm 0), .store (at_ .edi (hOff 3)) .eax] : List Instr) ++
    ([.alu .adc .ebx (.imm 0), .store (at_ .edi (hOff 4)) .ebx] : List Instr)))) := rfl

section
variable (st : BitVec 32) (s : State) (G : Nat → Nat) (d4 : Nat)
/-- After the carry into the words below `i`. -/
def CInv (i : Nat) (s' : State) : Prop :=
  VG.Proof.Poly1305.X86.After st s s' (fun k => if k < i then VG.Proof.Poly1305.X86.csum G d4 k % 2 ^ 32 else G k) [.eax, .ecx, .ebx] ∧
    s'.cf = some (decide (2 ^ 32 ≤ VG.Proof.Poly1305.X86.csum G d4 (i - 1))) ∧ VG.Proof.Poly1305.X86.v s' .ebx = d4 % 4
end

theorem shr2_toNat (x : BitVec 32) : (x >>> 2).toNat = x.toNat / 4 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem and3_toNat (x : BitVec 32) : (x &&& 3).toNat = x.toNat % 4 := by
  rw [BitVec.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod x.toNat 2

/-- `5 ⌊d4 / 4⌋ + t0`, with `d4 mod 4` left in `ebx`. -/
theorem carryHead_ok {st : BitVec 32} {s : State} (hc : VG.Proof.Poly1305.X86.Ctx st s) {G : Nat → Nat}
    (hw : VG.Proof.Poly1305.X86.Words s.mem st G) {d4 : Nat} (hd4 : VG.Proof.Poly1305.X86.v s .ebx = d4) (he : 5 * (d4 / 4) < 2 ^ 32) :
    WP isa (.block [.mov .eax (.reg .ebx), .shift .shr .eax 2, .mov .ecx (.reg .eax),
      .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .ecx),
      .alu .and .ebx (.imm 3), .alu .add .eax (.mem (at_ .edi (tOff 0))),
      .store (at_ .edi (hOff 0)) .eax]) s (VG.Proof.Poly1305.X86.CInv st s G d4 1) := by
  have hfit := hc.fit
  refine VG.Proof.Poly1305.X86.wp_mov fun s₁ u₁ _ => VG.Proof.Poly1305.X86.wp_shr (by decide) fun s₂ u₂ => VG.Proof.Poly1305.X86.wp_mov fun s₃ u₃ _ => ?_
  refine VG.Proof.Poly1305.X86.wp_addx (VG.Proof.Poly1305.X86.readSrc_reg _ _) fun s₄ u₄ _ => VG.Proof.Poly1305.X86.wp_addx (VG.Proof.Poly1305.X86.readSrc_reg _ _) fun s₅ u₅ _ => ?_
  refine VG.Proof.Poly1305.X86.wp_addx (VG.Proof.Poly1305.X86.readSrc_reg _ _) fun s₆ u₆ _ => VG.Proof.Poly1305.X86.wp_andx (VG.Proof.Poly1305.X86.readSrc_imm _ _) fun s₇ u₇ => ?_
  have edi₇ : s₇.gpr .edi = st := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hc.edi]
  have mem₇ : s₇.mem = s.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have rd₇ : s₇.rd = s.rd := by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₇ : s₇.wr = s.wr := by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  -- `eax = 5 ⌊d4 / 4⌋`.
  have q : (s₂.gpr .eax).toNat = d4 / 4 := by rw [u₂.gpr, u₁.gpr, VG.Proof.Poly1305.X86.shr2_toNat, ← hd4]
  have hq : d4 / 4 < 2 ^ 30 := by have := (s.gpr .ebx).isLt; simp only [VG.Proof.Poly1305.X86.v] at hd4; omega_using [he, q]
  have e₇ : (s₇.gpr .eax).toNat = 5 * (d4 / 4) := by
    rw [u₇.other .eax (by decide), u₆.gpr, u₅.gpr, u₅.other .ecx (by decide), u₄.gpr,
      u₄.other .ecx (by decide), u₃.gpr, u₃.other .eax (by decide)]
    simp only [BitVec.toNat_add, q]
    omega_using [he, q]
  have b₇ : VG.Proof.Poly1305.X86.v s₇ .ebx = d4 % 4 := by
    simp only [VG.Proof.Poly1305.X86.v]
    rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), VG.Proof.Poly1305.X86.and3_toNat]
    rw [← hd4]
  refine VG.Proof.Poly1305.X86.wp_addx (VG.Proof.Poly1305.X86.readSrc_mem (a := addr st (tOff 0)) (by rw [VG.Proof.Poly1305.X86.ea_at, edi₇])
    (by rw [rd₇, wr₇]; exact hc.inRW (by simp only [tOff, Nat.mul_zero, Nat.add_zero, Nat.reduceAdd, Nat.reduceLeDiff]) (by decide))) fun s₈ u₈ c₈ => ?_
  have t0 : (s₇.mem.readW (addr st (tOff 0)) 32).toNat = G 25 := by rw [mem₇]; exact hw 25 (by decide)
  refine VG.Proof.Poly1305.X86.wp_store (a := addr st (4 * 0)) (by rw [VG.Proof.Poly1305.X86.ea_at, u₈.other _ (by decide), edi₇]; rfl)
    (by rw [u₈.wr, wr₇]; exact hc.inW (by decide) (by decide)) fun s₉ u₉ => WP.block_nil ⟨⟨?_, ?_,
      fun r hr => ?_, by rw [u₉.rd, u₈.rd, rd₇], by rw [u₉.wr, u₈.wr, wr₇]⟩, ?_, ?_⟩
  · rw [u₉.mem, u₈.mem, mem₇]
    refine (hw.write hfit (by decide) _).congr fun k _ => ?_
    by_cases e : k = 0
    · subst e
      simp only [VG.Proof.Poly1305.X86.upd, ite_true, show (0 : Nat) < 1 by decide, VG.Proof.Poly1305.X86.csum]
      rw [u₈.gpr, BitVec.toNat_add, e₇, t0]
    · simp only [VG.Proof.Poly1305.X86.upd, e, ite_false, show ¬ k < 1 by omega_using [e]]
  · rw [u₉.mem, u₈.mem, mem₇]; exact VG.Proof.Poly1305.X86.frame_write (Frame.refl _ _) hfit (by decide) _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₉.gpr, u₈.other r hr.1, u₇.other r hr.2.2, u₆.other r hr.1, u₅.other r hr.1,
      u₄.other r hr.1, u₃.other r hr.2.1, u₂.other r hr.1, u₁.other r hr.1]
  · rw [u₉.cf, c₈, e₇, t0]; rfl
  · simp only [VG.Proof.Poly1305.X86.v]; rw [u₉.gpr, u₈.other _ (by decide)]; exact b₇

/-- The carry into word `i` (`1 ≤ i ≤ 3`). -/
theorem carryStep_ok {st : BitVec 32} {s : State} (hc : VG.Proof.Poly1305.X86.Ctx st s) {G : Nat → Nat}
    (hw : VG.Proof.Poly1305.X86.Words s.mem st G) {d4 : Nat} (he : 5 * (d4 / 4) < 2 ^ 32) {i : Nat} (hi : 1 ≤ i ∧ i < 4)
    {s' : State} (h : VG.Proof.Poly1305.X86.CInv st s G d4 i s') :
    WP isa (.block [.mov .eax (.mem (at_ .edi (tOff i))), .alu .adc .eax (.imm 0),
      .store (at_ .edi (hOff i)) .eax]) s' (VG.Proof.Poly1305.X86.CInv st s G d4 (i + 1)) := by
  obtain ⟨A, c, b⟩ := h
  have hlt := VG.Proof.Poly1305.X86.csum_lt (G := G) (d4 := d4) (fun k hk => hw.lt (by omega_using [hk])) he
  refine WP.mono (VG.Proof.Poly1305.X86.los_ok (A.ctx hc) A.words (j := 25 + i) (j' := i) (by simp only [tOff]; omega_using []) rfl
    (by omega_using [hi]) (by omega_using [hi]) (.inr ⟨rfl, c⟩) (VG.Proof.Poly1305.X86.src_imm 0)) fun s₁ ⟨A₁, c₁⟩ =>
      ⟨(A.trans A₁).mono.congr fun k _ => ?_, ?_, ?_⟩
  · simp only [VG.Proof.Poly1305.X86.upd]
    by_cases e : k = i
    · subst e
      simp only [ite_true, show ¬ 25 + k < k by omega_using [], ite_false, show k < k + 1 by omega_using []]
      rw [show (0 : BitVec 32).toNat = 0 from rfl, Nat.add_zero, VG.Proof.Poly1305.X86.carry_dec (hlt (k - 1) (by omega_using [hi]))]
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega_using [hi]⟩
      simp only [VG.Proof.Poly1305.X86.csum, show j + 1 ≠ 4 by omega_using [hi], ite_false, Nat.add_sub_cancel]
    · rw [ite_eq_right e]
      by_cases e' : k < i
      · simp only [e', ↓reduceIte, Nat.reducePow, show k < i + 1 by omega_using [e']]
      · simp only [e', ↓reduceIte, show ¬k < i + 1 by omega_using [e, e']]
  · rw [c₁]
    simp only [show i + 1 - 1 = i by omega_using [hi], show ¬ 25 + i < i by omega_using [], ite_false]
    rw [show (0 : BitVec 32).toNat = 0 from rfl, Nat.add_zero, VG.Proof.Poly1305.X86.carry_dec (hlt (i - 1) (by omega_using [hi]))]
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega_using [hi]⟩
    simp only [VG.Proof.Poly1305.X86.csum, show j + 1 ≠ 4 by omega_using [hi], ite_false, Nat.add_sub_cancel]
  · simp only [VG.Proof.Poly1305.X86.v]; rw [A₁.gpr _ (by decide)]; exact b

/-- The carries of `absorb`: the words `csum mod 2³²`. -/
theorem carry_ok {st : BitVec 32} {s : State} (hc : VG.Proof.Poly1305.X86.Ctx st s) {G : Nat → Nat}
    (hw : VG.Proof.Poly1305.X86.Words s.mem st G) {d4 : Nat} (hd4 : VG.Proof.Poly1305.X86.v s .ebx = d4) (he : 5 * (d4 / 4) < 2 ^ 32) :
    WP isa (.block VG.Impl.Poly1305.X86.carry) s fun s' =>
      VG.Proof.Poly1305.X86.After st s s' (fun k => if k < 5 then VG.Proof.Poly1305.X86.csum G d4 k % 2 ^ 32 else G k) [.eax, .ecx, .ebx] := by
  have hfit := hc.fit
  have hlt := VG.Proof.Poly1305.X86.csum_lt (G := G) (d4 := d4) (fun k hk => hw.lt (by omega_using [hk])) he
  rw [VG.Proof.Poly1305.X86.carry_eq]
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86.carryHead_ok hc hw hd4 he) fun s₁ h₁ => ?_)
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86.carryStep_ok hc hw he (i := 1) (by decide) h₁) fun s₂ h₂ => ?_)
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86.carryStep_ok hc hw he (i := 2) (by decide) h₂) fun s₃ h₃ => ?_)
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86.carryStep_ok hc hw he (i := 3) (by decide) h₃)
    fun s₄ ⟨A, c, b⟩ => ?_)
  have c₄ := A.ctx hc
  refine VG.Proof.Poly1305.X86.wp_adcx (VG.Proof.Poly1305.X86.readSrc_imm _ _) c fun s₅ u₅ c₅ => ?_
  refine VG.Proof.Poly1305.X86.wp_store (a := addr st (4 * 4)) (by rw [VG.Proof.Poly1305.X86.ea_at, u₅.other _ (by decide), c₄.edi]; rfl)
    (by rw [u₅.wr]; exact c₄.inW (by decide) (by decide)) fun s₆ u₆ => WP.block_nil ?_
  have A₆ : VG.Proof.Poly1305.X86.After st s₄ s₆ (VG.Proof.Poly1305.X86.upd (fun k => if k < 4 then VG.Proof.Poly1305.X86.csum G d4 k % 2 ^ 32 else G k) 4
      (s₅.gpr .ebx).toNat) [.ebx] := by
    refine ⟨?_, ?_, fun r hr => ?_, by rw [u₆.rd, u₅.rd], by rw [u₆.wr, u₅.wr]⟩
    · rw [u₆.mem, u₅.mem]; exact A.words.write hfit (j := 4) (by decide) _
    · rw [u₆.mem, u₅.mem]; exact VG.Proof.Poly1305.X86.frame_write (Frame.refl _ _) hfit (d := 4 * 4) (by decide) _
    · simp only [List.mem_singleton] at hr; rw [u₆.gpr, u₅.other r hr]
  refine (A.trans A₆).mono.congr fun k _ => ?_
  · simp only [VG.Proof.Poly1305.X86.upd]
    by_cases e : k = 4
    · subst e
      simp only [ite_true, show (4 : Nat) < 5 by decide]
      rw [u₅.gpr, VG.Proof.Poly1305.X86.add3_toNat, show (0 : BitVec 32).toNat = 0 from rfl, Nat.add_zero,
        VG.Proof.Poly1305.X86.carry_dec (hlt 3 (by decide))]
      simp only [VG.Proof.Poly1305.X86.v] at b
      rw [b]
      simp only [VG.Proof.Poly1305.X86.csum, ite_true, show (3 : Nat) + 1 = 4 from rfl]
    · rw [ite_eq_right e]
      by_cases e' : k < 4
      · simp only [e', ↓reduceIte, Nat.reducePow, show k < 5 by omega_using [e']]
      · simp only [e', ↓reduceIte, show ¬k < 5 by omega_using [e, e']]


/-! ## Absorbing a block -/

/-- The clamped `r` in the state's words: `r0`, `rj = 4 qj` and `sj = 5 qj`. -/
structure Coefs (f : Nat → Nat) (r0 q1 q2 q3 : Nat) : Prop where
  r0e : f 18 = r0
  r1e : f 19 = 4 * q1
  r2e : f 20 = 4 * q2
  r3e : f 21 = 4 * q3
  s1e : f 22 = 5 * q1
  s2e : f 23 = 5 * q2
  s3e : f 24 = 5 * q3
  r0_lt : r0 < 2 ^ 28
  q1_lt : q1 < 2 ^ 26
  q2_lt : q2 < 2 ^ 26
  q3_lt : q3 < 2 ^ 26

theorem Coefs.congr {f g : Nat → Nat} {r0 q1 q2 q3 : Nat} (h : VG.Proof.Poly1305.X86.Coefs f r0 q1 q2 q3)
    (he : ∀ k, 18 ≤ k → k < 25 → g k = f k) : VG.Proof.Poly1305.X86.Coefs g r0 q1 q2 q3 :=
  ⟨(he 18 (by decide) (by decide)).trans h.r0e, (he 19 (by decide) (by decide)).trans h.r1e,
    (he 20 (by decide) (by decide)).trans h.r2e, (he 21 (by decide) (by decide)).trans h.r3e,
    (he 22 (by decide) (by decide)).trans h.s1e, (he 23 (by decide) (by decide)).trans h.s2e,
    (he 24 (by decide) (by decide)).trans h.s3e, h.r0_lt, h.q1_lt, h.q2_lt, h.q3_lt⟩

section
variable (g : Nat → Nat)
theorem dterm0 : VG.Proof.Poly1305.X86.dterm g 0 = g 0 * g 18 + (g 1 * g 24 + (g 2 * g 23 + (g 3 * g 22 + 0))) := rfl
theorem dterm1 : VG.Proof.Poly1305.X86.dterm g 1 =
    g 0 * g 19 + (g 1 * g 18 + (g 2 * g 24 + (g 3 * g 23 + (g 4 * g 22 + 0)))) := rfl
theorem dterm2 : VG.Proof.Poly1305.X86.dterm g 2 =
    g 0 * g 20 + (g 1 * g 19 + (g 2 * g 18 + (g 3 * g 24 + (g 4 * g 23 + 0)))) := rfl
theorem dterm3 : VG.Proof.Poly1305.X86.dterm g 3 =
    g 0 * g 21 + (g 1 * g 20 + (g 2 * g 19 + (g 3 * g 18 + (g 4 * g 24 + 0)))) := rfl
end

/-- `h` in the state's words. -/
abbrev hw5 (f : Nat → Nat) : Nat := VG.Proof.Poly1305.X86.val5 (f 0) (f 1) (f 2) (f 3) (f 4)

theorem absorbAt_eq (b : Reg) (d : Nat) (pad : BitVec 32) :
    absorbAt b d pad = addBlock b d pad ++ (products ++ VG.Impl.Poly1305.X86.carry) := by
  simp only [absorbAt, List.append_assoc]

/-- Absorbing the block at `b + d`: from `h` with `h4 ≤ 4`, the new `h` is
congruent to `(h + m + pad · 2¹²⁸) r` modulo `p`, and its `h4` is at most 4. -/
theorem absorb_ok {st bp : BitVec 32} {b : Reg} {d : Nat} {s : State} {f : Nat → Nat}
    (hp : VG.Proof.Poly1305.X86.AddPre st bp b d s f)
    {r0 q1 q2 q3 : Nat} (hco : VG.Proof.Poly1305.X86.Coefs f r0 q1 q2 q3) (hh4 : f 4 ≤ 4) (pad : BitVec 32)
    (hpad : pad.toNat ≤ 1) :
    WP isa (.block (absorbAt b d pad)) s fun s' => ∃ g, VG.Proof.Poly1305.X86.After st s s' g [.eax, .ecx, .edx, .ebx, .ebp] ∧
      (∀ k, 5 ≤ k → k < 25 → g k = f k) ∧ (∀ k, 29 ≤ k → g k = f k) ∧
      VG.Proof.Poly1305.X86.hw5 g % P = ((VG.Proof.Poly1305.X86.hw5 f + (VG.Proof.Poly1305.X86.bw bp s 0 + 2 ^ 32 * VG.Proof.Poly1305.X86.bw bp s 1 + 2 ^ 64 * VG.Proof.Poly1305.X86.bw bp s 2 + 2 ^ 96 * VG.Proof.Poly1305.X86.bw bp s 3 +
        2 ^ 128 * pad.toNat)) * VG.Proof.Poly1305.X86.rval r0 q1 q2 q3) % P ∧ g 4 ≤ 4 := by
  have hc := hp.ctx
  have hf : ∀ k < 32, f k < 2 ^ 32 := fun k hk => hp.words.lt hk
  rw [VG.Proof.Poly1305.X86.absorbAt_eq]
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86.addBlock_ok hp pad) fun s₁ A₁ => ?_)
  -- The words of `h + m`.
  set a : Nat → Nat := fun k => if k < 5 then VG.Proof.Poly1305.X86.asum f (VG.Proof.Poly1305.X86.bw bp s) pad.toNat k % 2 ^ 32 else f k with ha
  have hlt := VG.Proof.Poly1305.X86.asum_lt (f := f) (b := VG.Proof.Poly1305.X86.bw bp s) (pad := pad.toNat) (fun k hk => hf k (by omega_using [hk]))
    (fun k _ => BitVec.isLt _) pad.isLt
  obtain ⟨hsum, ha4⟩ := VG.Proof.Poly1305.X86.add_arith (h0 := f 0) (h1 := f 1) (h2 := f 2) (h3 := f 3) (h4 := f 4)
    (m0 := VG.Proof.Poly1305.X86.bw bp s 0) (m1 := VG.Proof.Poly1305.X86.bw bp s 1) (m2 := VG.Proof.Poly1305.X86.bw bp s 2) (m3 := VG.Proof.Poly1305.X86.bw bp s 3) (pad := pad.toNat)
    (u0 := a 0) (u1 := a 1) (u2 := a 2) (u3 := a 3) (u4 := a 4) (hf 0 (by decide)) (hf 1 (by decide))
    (hf 2 (by decide)) (hf 3 (by decide)) hh4 (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _)
    (BitVec.isLt _) hpad (by simp only [ha, Nat.reducePow, Nat.zero_lt_succ, ↓reduceIte, VG.Proof.Poly1305.X86.asum]) (by simp only [ha, Nat.reducePow, Nat.reduceLT, ↓reduceIte, VG.Proof.Poly1305.X86.asum, Nat.zero_add, Nat.reduceEqDiff]) (by simp only [ha, Nat.reducePow, Nat.reduceLT, ↓reduceIte, VG.Proof.Poly1305.X86.asum, Nat.reduceAdd, Nat.reduceEqDiff, Nat.zero_add])
    (by simp only [ha, Nat.reducePow, Nat.reduceLT, ↓reduceIte, VG.Proof.Poly1305.X86.asum, Nat.reduceAdd, Nat.reduceEqDiff, Nat.zero_add]) (by simp only [ha, Nat.reducePow, Nat.lt_add_one, ↓reduceIte, VG.Proof.Poly1305.X86.asum, Nat.reduceAdd, Nat.reduceEqDiff, Nat.zero_add])
  have hco₁ : VG.Proof.Poly1305.X86.Coefs a r0 q1 q2 q3 := hco.congr fun k h₁ _ => by simp only [ha]; rw [ite_eq_right (by omega_using [h₁])]
  -- The sums of products.
  have ha' : ∀ k < 4, a k < 2 ^ 32 := fun k hk => by
    simp only [ha]; rw [ite_eq_left (by omega_using [hk])]; exact Nat.mod_lt _ (by decide)
  obtain ⟨b0, b1, b2, b3, b4, b5, hW⟩ := VG.Proof.Poly1305.X86.absorb_arith (a0 := a 0) (a1 := a 1) (a2 := a 2) (a3 := a 3)
    (a4 := a 4) (r0 := r0) (q1 := q1) (q2 := q2) (q3 := q3) (d0 := VG.Proof.Poly1305.X86.dv a 0) (d1 := VG.Proof.Poly1305.X86.dv a 1) (d2 := VG.Proof.Poly1305.X86.dv a 2)
    (d3 := VG.Proof.Poly1305.X86.dv a 3) (d4 := VG.Proof.Poly1305.X86.dv a 3 / 2 ^ 32 + a 4 * a 18) (ha' 0 (by decide)) (ha' 1 (by decide))
    (ha' 2 (by decide)) (ha' 3 (by decide)) ha4 hco.r0_lt hco.q1_lt hco.q2_lt hco.q3_lt
    (by rw [show VG.Proof.Poly1305.X86.dv a 0 = VG.Proof.Poly1305.X86.dterm a 0 from rfl, VG.Proof.Poly1305.X86.dterm0, hco₁.r0e, hco₁.s1e, hco₁.s2e, hco₁.s3e, Nat.zero_add])
    (by rw [show VG.Proof.Poly1305.X86.dv a 1 = VG.Proof.Poly1305.X86.dv a 0 / 2 ^ 32 + VG.Proof.Poly1305.X86.dterm a 1 from rfl, VG.Proof.Poly1305.X86.dterm1, hco₁.r0e, hco₁.r1e, hco₁.s1e, hco₁.s2e, hco₁.s3e])
    (by rw [show VG.Proof.Poly1305.X86.dv a 2 = VG.Proof.Poly1305.X86.dv a 1 / 2 ^ 32 + VG.Proof.Poly1305.X86.dterm a 2 from rfl, VG.Proof.Poly1305.X86.dterm2, hco₁.r0e, hco₁.r1e, hco₁.r2e, hco₁.s2e, hco₁.s3e])
    (by rw [show VG.Proof.Poly1305.X86.dv a 3 = VG.Proof.Poly1305.X86.dv a 2 / 2 ^ 32 + VG.Proof.Poly1305.X86.dterm a 3 from rfl, VG.Proof.Poly1305.X86.dterm3, hco₁.r0e, hco₁.r1e, hco₁.r2e, hco₁.r3e, hco₁.s3e])
    (by simp only [hco₁.r0e])
  have hb : ∀ k < 4, VG.Proof.Poly1305.X86.dv a k < 2 ^ 64 := fun k hk => by
    obtain rfl | rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega_using [hk]
    exacts [b0, b1, b2, b3]
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86.products_ok (A₁.ctx hc) A₁.words hb b4) fun s₂ ⟨A₂, e₂⟩ => ?_)
  -- The carries.
  refine WP.mono (VG.Proof.Poly1305.X86.carry_ok ((A₁.trans A₂).ctx hc) A₂.words e₂ b5) fun s₃ A₃ => ?_
  set d4 := VG.Proof.Poly1305.X86.dv a 3 / 2 ^ 32 + a 4 * a 18
  have hG : ∀ k < 4, VG.Proof.Poly1305.X86.dwords a 4 (25 + k) = VG.Proof.Poly1305.X86.dv a k % 2 ^ 32 := fun k hk => by
    simp only [VG.Proof.Poly1305.X86.dwords]; rw [ite_eq_left (by omega_using [hk])]; congr 2; omega_using [hk]
  obtain ⟨hu, hu4⟩ := VG.Proof.Poly1305.X86.carry_arith (t0 := VG.Proof.Poly1305.X86.dv a 0 % 2 ^ 32) (t1 := VG.Proof.Poly1305.X86.dv a 1 % 2 ^ 32) (t2 := VG.Proof.Poly1305.X86.dv a 2 % 2 ^ 32)
    (t3 := VG.Proof.Poly1305.X86.dv a 3 % 2 ^ 32) (d4 := d4) (e := 5 * (d4 / 4))
    (u0 := VG.Proof.Poly1305.X86.csum (VG.Proof.Poly1305.X86.dwords a 4) d4 0 % 2 ^ 32) (u1 := VG.Proof.Poly1305.X86.csum (VG.Proof.Poly1305.X86.dwords a 4) d4 1 % 2 ^ 32)
    (u2 := VG.Proof.Poly1305.X86.csum (VG.Proof.Poly1305.X86.dwords a 4) d4 2 % 2 ^ 32) (u3 := VG.Proof.Poly1305.X86.csum (VG.Proof.Poly1305.X86.dwords a 4) d4 3 % 2 ^ 32)
    (u4 := VG.Proof.Poly1305.X86.csum (VG.Proof.Poly1305.X86.dwords a 4) d4 4 % 2 ^ 32) (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
    (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) b5
    (by simp only [VG.Proof.Poly1305.X86.csum]; rw [← hG 0 (by decide)])
    (by simp only [VG.Proof.Poly1305.X86.csum]; rw [← hG 0 (by decide), ← hG 1 (by decide)]; rfl)
    (by simp only [VG.Proof.Poly1305.X86.csum]; rw [← hG 0 (by decide), ← hG 1 (by decide), ← hG 2 (by decide)]; rfl)
    (by simp only [VG.Proof.Poly1305.X86.csum]; rw [← hG 0 (by decide), ← hG 1 (by decide), ← hG 2 (by decide),
      ← hG 3 (by decide)]; rfl)
    (by simp only [VG.Proof.Poly1305.X86.csum]; rw [← hG 0 (by decide), ← hG 1 (by decide), ← hG 2 (by decide),
      ← hG 3 (by decide)]; rfl)
  refine ⟨_, ((A₁.trans A₂).trans A₃).mono, fun k h₁ h₂ => ?_, fun k h₁ => ?_, ?_, ?_⟩
  · simp only [VG.Proof.Poly1305.X86.dwords, ha]
    rw [ite_eq_right (by omega_using [h₁, h₂]), ite_eq_right (by omega_using [h₁, h₂]), ite_eq_right (by omega_using [h₁, h₂])]
  · simp only [VG.Proof.Poly1305.X86.dwords, ha]
    rw [ite_eq_right (by omega_using [h₁]), ite_eq_right (by omega_using [h₁]), ite_eq_right (by omega_using [h₁])]
  · simp only [VG.Proof.Poly1305.X86.hw5, show (0 : Nat) < 5 by decide, show (1 : Nat) < 5 by decide, show (2 : Nat) < 5 by decide,
      show (3 : Nat) < 5 by decide, show (4 : Nat) < 5 by decide, ite_true]
    rw [hu, hW, hsum]
  · simp only [show (4 : Nat) < 5 by decide, ite_true]; exact hu4

end VG.Proof.Poly1305.X86

end

/-!
# Poly1305 on x86 (32-bit): the final reduction
-/

namespace VG.Proof.Poly1305.X86

open VG VG.X86 VG.Impl.Poly1305.X86
open VG.Spec.Poly1305 (P)

/-! ## `g = h + 5` -/

section
variable (f : Nat → Nat)
/-- The sums of `h + 5`, with the carries. -/
def gsum : Nat → Nat
  | 0 => f 0 + 5
  | k + 1 => f (k + 1) + VG.Proof.Poly1305.X86.gsum k / 2 ^ 32
end

theorem gsum_lt {f : Nat → Nat} (hf : ∀ k < 5, f k < 2 ^ 32) : ∀ k < 5, VG.Proof.Poly1305.X86.gsum f k < 2 ^ 33 := by
  intro k hk
  induction k with
  | zero => have := hf 0 (by decide); simp only [VG.Proof.Poly1305.X86.gsum]; omega_using [this]
  | succ k ih => have := ih (by omega_using [hk]); have := hf (k + 1) hk; simp only [VG.Proof.Poly1305.X86.gsum]; omega

theorem plus5_eq : plus5 =
    ([.mov .eax (.mem (at_ .edi (hOff 0))), .alu .add .eax (.imm 5), .store (at_ .edi (tOff 0)) .eax] : List Instr) ++
    (([.mov .eax (.mem (at_ .edi (hOff 1))), .alu .adc .eax (.imm 0), .store (at_ .edi (tOff 1)) .eax] : List Instr) ++
    (([.mov .eax (.mem (at_ .edi (hOff 2))), .alu .adc .eax (.imm 0), .store (at_ .edi (tOff 2)) .eax] : List Instr) ++
    (([.mov .eax (.mem (at_ .edi (hOff 3))), .alu .adc .eax (.imm 0), .store (at_ .edi (tOff 3)) .eax] : List Instr) ++
    ([.mov .eax (.mem (at_ .edi (hOff 4))), .alu .adc .eax (.imm 0), .mov .edx (.reg .eax),
      .shift .shr .eax 2, .mov .ebp (.imm 0), .alu .sub .ebp (.reg .eax)] : List Instr)))) := rfl

section
variable (st : BitVec 32) (s : State) (f : Nat → Nat)
/-- After the words of `g` below `i`. -/
def GInv (i : Nat) (s' : State) : Prop :=
  VG.Proof.Poly1305.X86.After st s s' (fun k => if 25 ≤ k ∧ k < 25 + i then VG.Proof.Poly1305.X86.gsum f (k - 25) % 2 ^ 32 else f k) [.eax] ∧
    s'.cf = some (decide (2 ^ 32 ≤ VG.Proof.Poly1305.X86.gsum f (i - 1)))
end

theorem plus5Step_ok {st : BitVec 32} {s : State} (hc : VG.Proof.Poly1305.X86.Ctx st s) {f : Nat → Nat}
    (hw : VG.Proof.Poly1305.X86.Words s.mem st f) {i : Nat} (hi : 1 ≤ i ∧ i < 4) {s' : State} (h : VG.Proof.Poly1305.X86.GInv st s f i s') :
    WP isa (.block [.mov .eax (.mem (at_ .edi (hOff i))), .alu .adc .eax (.imm 0),
      .store (at_ .edi (tOff i)) .eax]) s' (VG.Proof.Poly1305.X86.GInv st s f (i + 1)) := by
  obtain ⟨A, c⟩ := h
  have hlt := VG.Proof.Poly1305.X86.gsum_lt (f := f) (fun k hk => hw.lt (by omega_using [hk]))
  refine WP.mono (VG.Proof.Poly1305.X86.los_ok (A.ctx hc) A.words (j := i) (j' := 25 + i) rfl (by simp only [tOff]; omega_using [])
    (by omega_using [hi]) (by omega_using [hi]) (.inr ⟨rfl, c⟩) (VG.Proof.Poly1305.X86.src_imm 0)) fun s₁ ⟨A₁, c₁⟩ =>
      ⟨(A.trans A₁).mono.congr fun k _ => ?_, ?_⟩
  · simp only [VG.Proof.Poly1305.X86.upd]
    rw [ite_eq_right (show ¬ (25 ≤ i ∧ i < 25 + i) by omega_using [hi]),
      show (0 : BitVec 32).toNat = 0 from rfl, Nat.add_zero, VG.Proof.Poly1305.X86.carry_dec (hlt (i - 1) (by omega_using [hi]))]
    by_cases e : k = 25 + i
    · subst e
      rw [ite_eq_left rfl, ite_eq_left ⟨by omega_using [hi], by omega_using []⟩]
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega_using [hi]⟩
      simp only [VG.Proof.Poly1305.X86.gsum, show 25 + (j + 1) - 25 = j + 1 by omega_using [hi], Nat.add_sub_cancel]
    · rw [ite_eq_right e]
      by_cases e' : 25 ≤ k ∧ k < 25 + i
      · rw [ite_eq_left e', ite_eq_left ⟨e'.1, by omega_using [e']⟩]
      · rw [ite_eq_right e', ite_eq_right (by omega_using [e, e'])]
  · rw [c₁]
    simp only [show i + 1 - 1 = i by omega_using [hi], show ¬ (25 ≤ i ∧ i < 25 + i) by omega_using [hi], ite_false]
    rw [show (0 : BitVec 32).toNat = 0 from rfl, Nat.add_zero, VG.Proof.Poly1305.X86.carry_dec (hlt (i - 1) (by omega_using [hi]))]
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega_using [hi]⟩
    simp only [VG.Proof.Poly1305.X86.gsum, Nat.add_sub_cancel]
    rfl

/-- `g = h + 5`: its low words stored, its top word `g4` in `edx`, and the
mask `-⌊g4 / 4⌋` in `ebp`. -/
theorem plus5_ok {st : BitVec 32} {s : State} (hc : VG.Proof.Poly1305.X86.Ctx st s) {f : Nat → Nat}
    (hw : VG.Proof.Poly1305.X86.Words s.mem st f) :
    WP isa (.block plus5) s fun s' =>
      VG.Proof.Poly1305.X86.After st s s' (fun k => if 25 ≤ k ∧ k < 29 then VG.Proof.Poly1305.X86.gsum f (k - 25) % 2 ^ 32 else f k)
        [.eax, .edx, .ebp] ∧
      VG.Proof.Poly1305.X86.v s' .edx = (f 4 + VG.Proof.Poly1305.X86.gsum f 3 / 2 ^ 32) % 2 ^ 32 ∧
      s'.gpr .ebp = 0 - (s'.gpr .edx >>> 2) := by
  have hlt := VG.Proof.Poly1305.X86.gsum_lt (f := f) (fun k hk => hw.lt (by omega_using [hk]))
  rw [VG.Proof.Poly1305.X86.plus5_eq]
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86.los_ok hc hw (j := 0) (j' := 25) rfl rfl (by decide) (by decide)
    (.inl ⟨rfl, rfl⟩) (VG.Proof.Poly1305.X86.src_imm 5)) fun s₁ ⟨A₁, c₁⟩ => ?_)
  have h₁ : VG.Proof.Poly1305.X86.GInv st s f 1 s₁ := ⟨A₁.congr fun k _ => ?_, by rw [c₁]; rfl⟩
  rotate_left
  · simp only [VG.Proof.Poly1305.X86.upd]
    by_cases e : k = 25
    · subst e; simp only [↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Bool.toNat_false, Nat.add_zero, Std.le_refl, Nat.reduceAdd, Nat.lt_add_one, and_self, Nat.sub_self, VG.Proof.Poly1305.X86.gsum]
    · rw [ite_eq_right e, ite_eq_right (by omega_using [e])]
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86.plus5Step_ok hc hw (i := 1) (by decide) h₁) fun s₂ h₂ => ?_)
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86.plus5Step_ok hc hw (i := 2) (by decide) h₂) fun s₃ h₃ => ?_)
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86.plus5Step_ok hc hw (i := 3) (by decide) h₃) fun s₄ ⟨A, c⟩ => ?_)
  have c₄ := A.ctx hc
  refine VG.Proof.Poly1305.X86.wp_movm (a := addr st (4 * 4)) (by rw [VG.Proof.Poly1305.X86.ea_at, c₄.edi]; rfl) (c₄.inRW (by decide) (by decide))
    fun s₅ u₅ cf₅ => ?_
  refine VG.Proof.Poly1305.X86.wp_adcx (VG.Proof.Poly1305.X86.readSrc_imm _ _) (by rw [cf₅]; exact c) fun s₆ u₆ _ => ?_
  refine VG.Proof.Poly1305.X86.wp_mov fun s₇ u₇ _ => VG.Proof.Poly1305.X86.wp_shr (by decide) fun s₈ u₈ => VG.Proof.Poly1305.X86.wp_movi fun s₉ u₉ _ => ?_
  refine VG.Proof.Poly1305.X86.wp_subx (VG.Proof.Poly1305.X86.readSrc_reg _ _) fun s₁₀ u₁₀ _ => WP.block_nil ⟨⟨?_, ?_, fun r hr => ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem]; exact A.words
  · rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem]; exact A.frame
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₁₀.other r hr.2.2, u₉.other r hr.2.2, u₈.other r hr.1, u₇.other r hr.2.1,
      u₆.other r hr.1, u₅.other r hr.1, A.gpr r (by simp only [List.mem_cons, hr.1, List.not_mem_nil, or_self, not_false_eq_true])]
  · rw [u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, A.rd]
  · rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, A.wr]
  · simp only [VG.Proof.Poly1305.X86.v]
    rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.gpr,
      VG.Proof.Poly1305.X86.add3_toNat, u₅.gpr, A.words.readW (k := 4) (by decide), show (0 : BitVec 32).toNat = 0 from rfl, Nat.add_zero,
      VG.Proof.Poly1305.X86.carry_dec (hlt 3 (by decide))]
    simp only [Nat.reduceLeDiff, Nat.reduceAdd, Nat.reduceLT, and_true, ↓reduceIte, Nat.reducePow]
  · rw [u₁₀.gpr, u₉.gpr, u₉.other _ (by decide), u₈.gpr, u₁₀.other _ (by decide),
      u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₇.other .eax (by decide)]
    rfl

/-! ## The selection -/

theorem select_false (x y : BitVec 32) : x ^^^ ((y ^^^ x) &&& 0) = x := by simp only [BitVec.ofNat_eq_ofNat, BitVec.and_zero, BitVec.xor_zero]
theorem select_true (x y : BitVec 32) : x ^^^ ((y ^^^ x) &&& BitVec.allOnes 32) = y := by
  rw [BitVec.and_allOnes, BitVec.xor_comm y, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- The mask for `b`. -/
def maskOf (b : Bool) : BitVec 32 := if b then BitVec.allOnes 32 else 0

theorem select_mask (x y : BitVec 32) (b : Bool) :
    (x ^^^ ((y ^^^ x) &&& VG.Proof.Poly1305.X86.maskOf b)).toNat = if b then y.toNat else x.toNat := by
  cases b
  · simp only [VG.Proof.Poly1305.X86.maskOf, Bool.false_eq_true, ite_false, VG.Proof.Poly1305.X86.select_false]
  · simp only [VG.Proof.Poly1305.X86.maskOf, ite_true, VG.Proof.Poly1305.X86.select_true]

/-- Word `k` of `h` replaced by that of `g` if `b`. -/
theorem selectWord_ok {st : BitVec 32} {s : State} (hc : VG.Proof.Poly1305.X86.Ctx st s) {f : Nat → Nat}
    (hw : VG.Proof.Poly1305.X86.Words s.mem st f) {k : Nat} (hk : k < 4) {b : Bool} (hm : s.gpr .ebp = VG.Proof.Poly1305.X86.maskOf b) :
    WP isa (.block (selectWord k)) s fun s' =>
      VG.Proof.Poly1305.X86.After st s s' (VG.Proof.Poly1305.X86.upd f k (if b then f (25 + k) else f k)) [.eax, .ecx] := by
  have hfit := hc.fit
  refine VG.Proof.Poly1305.X86.wp_movm (a := addr st (4 * k)) (by rw [VG.Proof.Poly1305.X86.ea_at, hc.edi]; rfl) (hc.inRW (by omega_using [hk]) (by decide))
    fun s₁ u₁ _ => ?_
  have ht : tOff k = 4 * (25 + k) := by simp only [tOff]; omega_using []
  refine VG.Proof.Poly1305.X86.wp_movm (a := addr st (4 * (25 + k))) (by rw [VG.Proof.Poly1305.X86.ea_at, u₁.other .edi (by decide), hc.edi, ht])
    (by rw [u₁.rd, u₁.wr]; exact hc.inRW (by omega_using [hk]) (by decide)) fun s₂ u₂ _ => ?_
  refine VG.Proof.Poly1305.X86.wp_xorx (VG.Proof.Poly1305.X86.readSrc_reg _ _) fun s₃ u₃ => VG.Proof.Poly1305.X86.wp_andx (VG.Proof.Poly1305.X86.readSrc_reg _ _) fun s₄ u₄ => ?_
  refine VG.Proof.Poly1305.X86.wp_xorx (VG.Proof.Poly1305.X86.readSrc_reg _ _) fun s₅ u₅ => ?_
  have edi₅ : s₅.gpr .edi = st := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hc.edi]
  have mem₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine VG.Proof.Poly1305.X86.wp_store (a := addr st (4 * k)) (by rw [VG.Proof.Poly1305.X86.ea_at, edi₅]; rfl)
    (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hc.inW (by omega_using [hk]) (by decide))
    fun s₆ u₆ => WP.block_nil ⟨?_, ?_, fun r hr => ?_, ?_, ?_⟩
  · rw [u₆.mem, mem₅]
    refine (hw.write hfit (by omega_using [hk]) _).congr fun j _ => ?_
    simp only [VG.Proof.Poly1305.X86.upd]
    split
    · rw [u₅.gpr, u₄.other .eax (by decide), u₄.gpr, u₃.other .eax (by decide),
        u₃.other .ebp (by decide), u₃.gpr, u₂.gpr, u₂.other .eax (by decide), u₂.other .ebp (by decide),
        u₁.gpr, u₁.other .ebp (by decide), hm, u₁.mem, VG.Proof.Poly1305.X86.select_mask, hw.readW (k := k) (by omega_using [hk]),
        hw.readW (k := 25 + k) (by omega_using [hk])]
    · rfl
  · rw [u₆.mem, mem₅]; exact VG.Proof.Poly1305.X86.frame_write (Frame.refl _ _) hfit (by omega_using [hk]) _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₆.gpr, u₅.other r hr.1, u₄.other r hr.2, u₃.other r hr.2, u₂.other r hr.2, u₁.other r hr.1]
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]


/-- The low words selected, from the words `f` (`h` and, at `25 + k`, `g`). -/
def selWords (f : Nat → Nat) (b : Bool) (n : Nat) : Nat → Nat :=
  fun k => if k < n then (if b then f (25 + k) else f k) else f k

theorem selects_ok {st : BitVec 32} {s : State} (hc : VG.Proof.Poly1305.X86.Ctx st s) {f : Nat → Nat}
    (hw : VG.Proof.Poly1305.X86.Words s.mem st f) {b : Bool} (hm : s.gpr .ebp = VG.Proof.Poly1305.X86.maskOf b) :
    ∀ n ≤ 4, WP isa (.block ((List.range n).flatMap selectWord)) s fun s' =>
      VG.Proof.Poly1305.X86.After st s s' (VG.Proof.Poly1305.X86.selWords f b n) [.eax, .ecx] := by
  intro n hn
  induction n with
  | zero => exact WP.block_nil ⟨hw.congr fun k _ => by simp only [VG.Proof.Poly1305.X86.selWords, Nat.not_lt_zero, ↓reduceIte], Frame.refl _ _,
      fun _ _ => rfl, rfl, rfl⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (ih (by omega_using [hn])) fun s₁ A₁ => ?_)
    refine WP.mono (VG.Proof.Poly1305.X86.selectWord_ok (A₁.ctx hc) A₁.words (k := n) (by omega_using [hn])
      (by rw [A₁.gpr _ (by decide)]; exact hm)) fun s₂ A₂ => (A₁.trans A₂).mono.congr fun k _ => ?_
    by_cases e : k = n
    · subst e
      simp only [VG.Proof.Poly1305.X86.upd, VG.Proof.Poly1305.X86.selWords, ite_true, show ¬ 25 + k < k by omega_using [], show ¬ k < k by omega_using [],
        ite_false, show k < k + 1 by omega_using []]
    · simp only [VG.Proof.Poly1305.X86.upd, VG.Proof.Poly1305.X86.selWords, e, ite_false]
      by_cases e' : k < n
      · simp only [e', ite_true, show k < n + 1 by omega_using [e']]
      · simp only [e', ite_false, show ¬ k < n + 1 by omega_using [e, e']]

/-- The top word: that of `g` (in `edx`) or of `h`, modulo 4. -/
theorem selectTop_ok {st : BitVec 32} {s : State} (hc : VG.Proof.Poly1305.X86.Ctx st s) {f : Nat → Nat}
    (hw : VG.Proof.Poly1305.X86.Words s.mem st f) {b : Bool} (hm : s.gpr .ebp = VG.Proof.Poly1305.X86.maskOf b) :
    WP isa (.block selectTop) s fun s' =>
      VG.Proof.Poly1305.X86.After st s s' (VG.Proof.Poly1305.X86.upd f 4 ((if b then VG.Proof.Poly1305.X86.v s .edx else f 4) % 4)) [.eax, .edx] := by
  have hfit := hc.fit
  refine VG.Proof.Poly1305.X86.wp_movm (a := addr st (4 * 4)) (by rw [VG.Proof.Poly1305.X86.ea_at, hc.edi]; rfl) (hc.inRW (by decide) (by decide))
    fun s₁ u₁ _ => ?_
  refine VG.Proof.Poly1305.X86.wp_xorx (VG.Proof.Poly1305.X86.readSrc_reg _ _) fun s₂ u₂ => VG.Proof.Poly1305.X86.wp_andx (VG.Proof.Poly1305.X86.readSrc_reg _ _) fun s₃ u₃ => ?_
  refine VG.Proof.Poly1305.X86.wp_xorx (VG.Proof.Poly1305.X86.readSrc_reg _ _) fun s₄ u₄ => VG.Proof.Poly1305.X86.wp_andx (VG.Proof.Poly1305.X86.readSrc_imm _ _) fun s₅ u₅ => ?_
  have edi₅ : s₅.gpr .edi = st := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hc.edi]
  have mem₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine VG.Proof.Poly1305.X86.wp_store (a := addr st (4 * 4)) (by rw [VG.Proof.Poly1305.X86.ea_at, edi₅]; rfl)
    (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hc.inW (by decide) (by decide))
    fun s₆ u₆ => WP.block_nil ⟨?_, ?_, fun r hr => ?_, ?_, ?_⟩
  · rw [u₆.mem, mem₅]
    refine (hw.write hfit (by decide) _).congr fun j _ => ?_
    simp only [VG.Proof.Poly1305.X86.upd]
    split
    · rw [u₅.gpr, VG.Proof.Poly1305.X86.and3_toNat, u₄.gpr, u₃.other .eax (by decide), u₃.gpr, u₂.other .eax (by decide),
        u₂.other .ebp (by decide), u₂.gpr, u₁.gpr, u₁.other .edx (by decide), u₁.other .ebp (by decide),
        hm, VG.Proof.Poly1305.X86.select_mask, hw.readW (k := 4) (by decide)]
    · rfl
  · rw [u₆.mem, mem₅]; exact VG.Proof.Poly1305.X86.frame_write (Frame.refl _ _) hfit (by decide) _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₆.gpr, u₅.other r hr.1, u₄.other r hr.1, u₃.other r hr.2, u₂.other r hr.2, u₁.other r hr.1]
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]

theorem reduce_eq : reduce = plus5 ++ ((List.range 4).flatMap selectWord ++ selectTop) := by
  simp only [reduce, List.append_assoc]

theorem mask_of {g4 : Nat} (hg : g4 ≤ 5) (x : BitVec 32) (hx : x.toNat = g4) :
    (0 : BitVec 32) - (x >>> 2) = VG.Proof.Poly1305.X86.maskOf (decide (g4 / 4 = 1)) := by
  have hs : (x >>> 2).toNat = g4 / 4 := by rw [VG.Proof.Poly1305.X86.shr2_toNat, hx]
  rcases (by omega_using [hg, hx, hs] : g4 / 4 = 1 ∨ g4 / 4 = 0) with h | h
  · rw [h] at hs
    rw [show x >>> 2 = 1 from BitVec.eq_of_toNat_eq hs, h]; rfl
  · rw [h] at hs
    rw [show x >>> 2 = 0 from BitVec.eq_of_toNat_eq hs, h]; rfl

/-- `h` reduced fully, in place: its words are those of `h mod p`, the top one less than 4. -/
theorem reduce_ok {st : BitVec 32} {s : State} (hc : VG.Proof.Poly1305.X86.Ctx st s) {f : Nat → Nat}
    (hw : VG.Proof.Poly1305.X86.Words s.mem st f) (h4 : f 4 ≤ 4) :
    WP isa (.block reduce) s fun s' => ∃ g, VG.Proof.Poly1305.X86.After st s s' g [.eax, .ecx, .edx, .ebp] ∧
      (∀ k, 5 ≤ k → k < 25 → g k = f k) ∧ (∀ k, 29 ≤ k → g k = f k) ∧
      VG.Proof.Poly1305.X86.hw5 g = VG.Proof.Poly1305.X86.hw5 f % P ∧ g 4 < 4 := by
  have hf : ∀ k < 32, f k < 2 ^ 32 := fun k hk => hw.lt hk
  rw [VG.Proof.Poly1305.X86.reduce_eq]
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86.plus5_ok hc hw) fun s₁ ⟨A₁, e₁, m₁⟩ => ?_)
  -- The mask.
  set G : Nat → Nat := fun k => if 25 ≤ k ∧ k < 29 then VG.Proof.Poly1305.X86.gsum f (k - 25) % 2 ^ 32 else f k with hG
  set g4 := (f 4 + VG.Proof.Poly1305.X86.gsum f 3 / 2 ^ 32) % 2 ^ 32
  have hlt := VG.Proof.Poly1305.X86.gsum_lt (f := f) (fun k hk => hf k (by omega_using [hk]))
  have hg4 : g4 ≤ 5 := by
    have := hlt 3 (by decide); have := hf 4 (by decide); simp only [g4]; omega
  have m₁' := m₁.trans (VG.Proof.Poly1305.X86.mask_of hg4 _ e₁)
  set b := decide (g4 / 4 = 1) with hb
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86.selects_ok (A₁.ctx hc) A₁.words m₁' 4 (Nat.le_refl _)) fun s₂ A₂ => ?_)
  refine WP.mono (VG.Proof.Poly1305.X86.selectTop_ok ((A₁.trans A₂).ctx hc) A₂.words (by rw [A₂.gpr _ (by decide)]; exact m₁'))
    fun s₃ A₃ => ⟨_, ((A₁.trans A₂).trans A₃).mono, fun k h₁ h₂ => ?_, fun k h₁ => ?_, ?_, ?_⟩
  · simp only [VG.Proof.Poly1305.X86.upd, VG.Proof.Poly1305.X86.selWords, hG]
    rw [ite_eq_right (by omega_using [h₁, h₂]), ite_eq_right (by omega_using [h₁, h₂]), ite_eq_right (by omega_using [h₁, h₂])]
  · simp only [VG.Proof.Poly1305.X86.upd, VG.Proof.Poly1305.X86.selWords, hG]
    rw [ite_eq_right (by omega_using [h₁]), ite_eq_right (by omega_using [h₁]), ite_eq_right (by omega_using [h₁])]
  · have ed : VG.Proof.Poly1305.X86.v s₂ .edx = g4 := by simp only [VG.Proof.Poly1305.X86.v]; rw [A₂.gpr _ (by decide)]; exact e₁
    simp only [VG.Proof.Poly1305.X86.hw5, VG.Proof.Poly1305.X86.upd, VG.Proof.Poly1305.X86.selWords, hG, ed, ite_true,
      show (0 : Nat) ≠ 4 by decide, show (1 : Nat) ≠ 4 by decide, show (2 : Nat) ≠ 4 by decide,
      show (3 : Nat) ≠ 4 by decide, ite_false, show (0 : Nat) < 4 by decide,
      show (1 : Nat) < 4 by decide, show (2 : Nat) < 4 by decide, show (3 : Nat) < 4 by decide,
      show ¬ (4 : Nat) < 4 by decide]
    rcases VG.Proof.Poly1305.X86.reduce_arith (h0 := f 0) (h1 := f 1) (h2 := f 2) (h3 := f 3) (h4 := f 4)
      (g0 := VG.Proof.Poly1305.X86.gsum f 0 % 2 ^ 32) (g1 := VG.Proof.Poly1305.X86.gsum f 1 % 2 ^ 32) (g2 := VG.Proof.Poly1305.X86.gsum f 2 % 2 ^ 32)
      (g3 := VG.Proof.Poly1305.X86.gsum f 3 % 2 ^ 32) (g4 := g4) (hf 0 (by decide)) (hf 1 (by decide)) (hf 2 (by decide))
      (hf 3 (by decide)) h4 rfl rfl rfl rfl rfl with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hbt : b = true := by rw [hb, h1]; rfl
      simp only [↓reduceIte, Nat.reduceLT, Nat.reduceLeDiff, Nat.reducePow, and_self, hbt, Nat.reduceAdd, Nat.reduceSub]
      exact h2
    · have hbt : b = false := by rw [hb, h1]; rfl
      simp only [↓reduceIte, Nat.reduceLT, Nat.reduceLeDiff, Nat.reducePow, hbt, Bool.false_eq_true,
        Nat.reduceSub]
      exact h2
  · simp only [VG.Proof.Poly1305.X86.upd, ite_true]; exact Nat.mod_lt _ (by decide)

end VG.Proof.Poly1305.X86

end

-- Formerly the module `VerifiedGarbage.Proof.Poly1305.X86.Run`.
section

section

/-!
# Poly1305 on x86 (32-bit): the state in memory, as the specification sees it

Little-endian numbers of 32-bit words in memory, the key and its clamped `r`,
and the tag.
-/

namespace VG.Proof.Poly1305.X86

open VG VG.X86 VG.Impl.Poly1305.X86
open VG.Spec.Poly1305 (P clamp leNum leBytes bytesAt accumulate Repr)

/-! ## Numbers as words -/

theorem leNum_bytesAt_4 (m : Mem) (p : Addr) : leNum (bytesAt m p 4) = (m.readW p 32).toNat := by
  rw [Poly1305.leNum_bytesAt_read]; simp only [Nat.reduceMul, Mem.readW, Nat.reduceDiv, BitVec.setWidth_eq]

theorem leNum_bytesAt_4add (m : Mem) (p : Addr) (n : Nat) :
    leNum (bytesAt m p (4 + n)) =
      (m.readW p 32).toNat + 2 ^ 32 * leNum (bytesAt m (p + BitVec.ofNat 64 4) n) := by
  rw [Poly1305.bytesAt_add, Poly1305.leNum_append, Poly1305.length_bytesAt, VG.Proof.Poly1305.X86.leNum_bytesAt_4]

/-- The word at `p + 4 k`, as a number. -/
abbrev w32 (m : Mem) (p : Addr) (k : Nat) : Nat := (m.readW (p + BitVec.ofNat 64 (4 * k)) 32).toNat

theorem add_ofNat_add (p : Addr) (d e : Nat) :
    p + BitVec.ofNat 64 d + BitVec.ofNat 64 e = p + BitVec.ofNat 64 (d + e) := Offset.add_add p d e

/-- Four little-endian words. -/
theorem leNum_bytesAt_16 (m : Mem) (p : Addr) :
    leNum (bytesAt m p 16) = VG.Proof.Poly1305.X86.w32 m p 0 + 2 ^ 32 * VG.Proof.Poly1305.X86.w32 m p 1 + 2 ^ 64 * VG.Proof.Poly1305.X86.w32 m p 2 + 2 ^ 96 * VG.Proof.Poly1305.X86.w32 m p 3 := by
  rw [show 16 = 4 + (4 + (4 + (4 + 0))) from rfl, VG.Proof.Poly1305.X86.leNum_bytesAt_4add, VG.Proof.Poly1305.X86.leNum_bytesAt_4add,
    VG.Proof.Poly1305.X86.leNum_bytesAt_4add, VG.Proof.Poly1305.X86.leNum_bytesAt_4add]
  simp only [VG.Proof.Poly1305.X86.w32, VG.Proof.Poly1305.X86.add_ofNat_add, show bytesAt m _ 0 = [] from rfl, Spec.Poly1305.leNum, BitVec.add_zero,
    Nat.mul_zero, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd]
  omega_using []

/-- Six little-endian words. -/
theorem leNum_bytesAt_24 (m : Mem) (p : Addr) :
    leNum (bytesAt m p 24) = VG.Proof.Poly1305.X86.w32 m p 0 + 2 ^ 32 * VG.Proof.Poly1305.X86.w32 m p 1 + 2 ^ 64 * VG.Proof.Poly1305.X86.w32 m p 2 + 2 ^ 96 * VG.Proof.Poly1305.X86.w32 m p 3 +
      2 ^ 128 * VG.Proof.Poly1305.X86.w32 m p 4 + 2 ^ 160 * VG.Proof.Poly1305.X86.w32 m p 5 := by
  rw [show 24 = 4 + (4 + (4 + (4 + (4 + (4 + 0))))) from rfl, VG.Proof.Poly1305.X86.leNum_bytesAt_4add, VG.Proof.Poly1305.X86.leNum_bytesAt_4add,
    VG.Proof.Poly1305.X86.leNum_bytesAt_4add, VG.Proof.Poly1305.X86.leNum_bytesAt_4add, VG.Proof.Poly1305.X86.leNum_bytesAt_4add, VG.Proof.Poly1305.X86.leNum_bytesAt_4add]
  simp only [VG.Proof.Poly1305.X86.w32, VG.Proof.Poly1305.X86.add_ofNat_add, show bytesAt m _ 0 = [] from rfl, Spec.Poly1305.leNum, BitVec.add_zero,
    Nat.mul_zero, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd]
  omega_using []

/-- A word of the state as the specification addresses it. -/
theorem w32_eq {m : Mem} {st : BitVec 32} (hfit : st.toNat + 128 ≤ 2 ^ 32) {k : Nat} (hk : k < 32) :
    VG.Proof.Poly1305.X86.w32 m (st.setWidth 64) k = VG.Proof.Poly1305.X86.wv m st (4 * k) := by
  rw [VG.Proof.Poly1305.X86.wv, VG.Proof.Poly1305.X86.wd, addr_eq (by omega_using [hfit, hk])]

theorem w32_off {m : Mem} {st : BitVec 32} (hfit : st.toNat + 128 ≤ 2 ^ 32) {d k : Nat}
    (hk : d + 4 * k + 4 ≤ 128) : VG.Proof.Poly1305.X86.w32 m (st.setWidth 64 + BitVec.ofNat 64 d) k = VG.Proof.Poly1305.X86.wv m st (d + 4 * k) := by
  simp only [VG.Proof.Poly1305.X86.w32, VG.Proof.Poly1305.X86.wv, VG.Proof.Poly1305.X86.wd]
  rw [addr_eq (by omega_using [hfit, hk]), VG.Proof.Poly1305.X86.add_ofNat_add]

/-- The accumulator in the state's words. -/
theorem leNum_acc {m : Mem} {st : BitVec 32} (hfit : st.toNat + 128 ≤ 2 ^ 32) {f : Nat → Nat}
    (hw : VG.Proof.Poly1305.X86.Words m st f) :
    leNum (bytesAt m (st.setWidth 64) 24) = VG.Proof.Poly1305.X86.hw5 f + 2 ^ 160 * f 5 := by
  rw [VG.Proof.Poly1305.X86.leNum_bytesAt_24, VG.Proof.Poly1305.X86.w32_eq hfit (by decide), VG.Proof.Poly1305.X86.w32_eq hfit (by decide), VG.Proof.Poly1305.X86.w32_eq hfit (by decide),
    VG.Proof.Poly1305.X86.w32_eq hfit (by decide), VG.Proof.Poly1305.X86.w32_eq hfit (by decide), VG.Proof.Poly1305.X86.w32_eq hfit (by decide), hw 0 (by decide),
    hw 1 (by decide), hw 2 (by decide), hw 3 (by decide), hw 4 (by decide), hw 5 (by decide)]
  rfl

/-- The accumulator of a state that represents a message, below `p`, as words. -/
theorem acc_words {m : Mem} {st : BitVec 32} (hfit : st.toNat + 128 ≤ 2 ^ 32) {f : Nat → Nat}
    (hw : VG.Proof.Poly1305.X86.Words m st f) (hlt : leNum (bytesAt m (st.setWidth 64) 24) < P) :
    f 5 = 0 ∧ f 4 ≤ 3 ∧ leNum (bytesAt m (st.setWidth 64) 24) = VG.Proof.Poly1305.X86.hw5 f := by
  rw [VG.Proof.Poly1305.X86.leNum_acc hfit hw] at hlt ⊢
  have h0 := hw.lt (k := 0) (by decide); have h1 := hw.lt (k := 1) (by decide)
  have h2 := hw.lt (k := 2) (by decide); have h3 := hw.lt (k := 3) (by decide)
  simp only [VG.Proof.Poly1305.X86.hw5, VG.Proof.Poly1305.X86.val5, P] at hlt ⊢
  omega_using [hlt, h0, h1, h2, h3]

/-! ## Bytes as words -/

/-- Bytes of memory are the same where the words are. -/
theorem bytesAt_congr_words2 {m m' : Mem} {p q : Addr} {n : Nat}
    (h : ∀ k < n, m'.readW (p + BitVec.ofNat 64 (4 * k)) 32 = m.readW (q + BitVec.ofNat 64 (4 * k)) 32) :
    bytesAt m' p (4 * n) = bytesAt m q (4 * n) := by
  simp only [bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  have e : ∀ x : Addr, x + BitVec.ofNat 64 i = (x + BitVec.ofNat 64 (4 * (i / 4))) + BitVec.ofNat 64 (i % 4) :=
    fun x => by rw [VG.Proof.Poly1305.X86.add_ofNat_add]; congr 2; omega_using []
  rw [e p, e q, Mem.readW_byte m' _ (Nat.mod_lt _ (by decide)), Mem.readW_byte m _ (Nat.mod_lt _ (by decide)),
    h _ (by omega_using [hi])]

theorem bytesAt_congr_words {m m' : Mem} {p : Addr} {n : Nat}
    (h : ∀ k < n, m'.readW (p + BitVec.ofNat 64 (4 * k)) 32 = m.readW (p + BitVec.ofNat 64 (4 * k)) 32) :
    bytesAt m' p (4 * n) = bytesAt m p (4 * n) := VG.Proof.Poly1305.X86.bytesAt_congr_words2 h

/-! ## The key -/

theorem land_split32 {a b c d : Nat} (ha : a < 2 ^ 32) (hc : c < 2 ^ 32) :
    (a + 2 ^ 32 * b) &&& (c + 2 ^ 32 * d) = (a &&& c) + 2 ^ 32 * (b &&& d) := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hac : (a &&& c) < 2 ^ 32 := Nat.lt_of_le_of_lt Nat.and_le_left ha
  rw [Nat.testBit_and]
  rw [Nat.add_comm a, Nat.add_comm c, Nat.add_comm (a &&& c)]
  rw [Nat.testBit_two_pow_mul_add _ ha, Nat.testBit_two_pow_mul_add _ hc,
    Nat.testBit_two_pow_mul_add _ hac]
  split <;> simp only [Nat.testBit_and]

/-- The clamped `r` of a key of four little-endian words. -/
theorem clamp_words4 {k0 k1 k2 k3 : Nat} (h0 : k0 < 2 ^ 32) (h1 : k1 < 2 ^ 32) (h2 : k2 < 2 ^ 32) :
    clamp (k0 + 2 ^ 32 * k1 + 2 ^ 64 * k2 + 2 ^ 96 * k3) =
      (k0 &&& 0x0fffffff) + 2 ^ 32 * (k1 &&& 0x0ffffffc) + 2 ^ 64 * (k2 &&& 0x0ffffffc) +
        2 ^ 96 * (k3 &&& 0x0ffffffc) := by
  have e : ∀ x y z w : Nat, x + 2 ^ 32 * y + 2 ^ 64 * z + 2 ^ 96 * w =
      x + 2 ^ 32 * (y + 2 ^ 32 * (z + 2 ^ 32 * w)) := fun x y z w => by omega_using []
  rw [clamp, e, show (0x0ffffffc0ffffffc0ffffffc0fffffff : Nat) =
    0x0fffffff + 2 ^ 32 * (0x0ffffffc + 2 ^ 32 * (0x0ffffffc + 2 ^ 32 * 0x0ffffffc)) from rfl,
    VG.Proof.Poly1305.X86.land_split32 h0 (by decide), VG.Proof.Poly1305.X86.land_split32 h1 (by decide), VG.Proof.Poly1305.X86.land_split32 h2 (by decide), e]

theorem mask0_lt (k : Nat) : k &&& 0x0fffffff < 2 ^ 28 :=
  Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem mask1_lt (k : Nat) : k &&& 0x0ffffffc < 2 ^ 28 :=
  Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem mask1_mod (k : Nat) : (k &&& 0x0ffffffc) % 4 = 0 := by
  rw [show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.and_two_pow_sub_one_eq_mod, Nat.and_assoc,
    show (0x0ffffffc : Nat) &&& 2 ^ 2 - 1 = 0 by decide, Nat.and_zero]

/-! ## The tag -/

theorem bytesAt_leBytes_4 (m : Mem) (p : Addr) : bytesAt m p 4 = leBytes 4 (m.readW p 32).toNat := by
  rw [Poly1305.bytesAt_leBytes]; simp only [Nat.reduceMul, Mem.readW, Nat.reduceDiv, BitVec.setWidth_eq]

/-- Four little-endian words in memory are the 16 bytes of `x`, if they are its
low 128 bits. -/
theorem bytesAt_leBytes_16w (m : Mem) (p : Addr) (x : Nat) (h : ∀ k < 4, VG.Proof.Poly1305.X86.w32 m p k = x / 2 ^ (32 * k) % 2 ^ 32) :
    bytesAt m p 16 = leBytes 16 x := by
  have e : ∀ k < 4, bytesAt m (p + BitVec.ofNat 64 (4 * k)) 4 = leBytes 4 (x / 2 ^ (32 * k)) := by
    intro k hk
    rw [VG.Proof.Poly1305.X86.bytesAt_leBytes_4, show (m.readW (p + BitVec.ofNat 64 (4 * k)) 32).toNat = VG.Proof.Poly1305.X86.w32 m p k from rfl,
      h k hk, show (2 : Nat) ^ 32 = 256 ^ 4 from rfl, Poly1305.leBytes_mod]
  rw [show 16 = 4 + (4 + (4 + 4)) from rfl, Poly1305.bytesAt_add, Poly1305.bytesAt_add,
    Poly1305.bytesAt_add, Poly1305.leBytes_add, Poly1305.leBytes_add, Poly1305.leBytes_add,
    VG.Proof.Poly1305.X86.add_ofNat_add, VG.Proof.Poly1305.X86.add_ofNat_add]
  have e0 := e 0 (by decide); have e1 := e 1 (by decide); have e2 := e 2 (by decide)
  have e3 := e 3 (by decide)
  simp only [Nat.mul_zero, BitVec.add_zero, Nat.pow_zero, Nat.div_one] at e0
  rw [e0, e1, e2, e3, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, ← Nat.pow_add, ← Nat.pow_add]

end VG.Proof.Poly1305.X86

end

section

/-!
# Poly1305 on x86 (32-bit): saving registers and clamping the key
-/

namespace VG.Proof.Poly1305.X86

open VG VG.X86 VG.Impl.Poly1305.X86

/-- The state's words on entry. -/
def words (m : Mem) (st : BitVec 32) : Nat → Nat := fun k => VG.Proof.Poly1305.X86.wv m st (4 * k)

theorem words_ok (m : Mem) (st : BitVec 32) : VG.Proof.Poly1305.X86.Words m st (VG.Proof.Poly1305.X86.words m st) := fun _ _ => rfl

theorem save_eq : save = [.mov .eax (.mem (at_ .esp 4)), .store (at_ .eax 116) .ebx,
    .store (at_ .eax 120) .esi, .store (at_ .eax 124) .edi, .store (at_ .eax 20) .ebp,
    .mov .edi (.reg .eax)] := rfl

/-- The callee-saved registers of `s`, saved in the words `f`. -/
def SavedIn (s : State) (f : Nat → Nat) : Prop :=
  f 29 = VG.Proof.Poly1305.X86.v s .ebx ∧ f 30 = VG.Proof.Poly1305.X86.v s .esi ∧ f 31 = VG.Proof.Poly1305.X86.v s .edi ∧ f 5 = VG.Proof.Poly1305.X86.v s .ebp

/-- The state at `[esp + 4]` into `edi`, saving `ebx, esi, edi, ebp` in it. -/
theorem save_ok {s : State} {st : BitVec 32} (hst : s.mem.readW (addr (s.gpr .esp) 4) 32 = st)
    (harg : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 4) 4) (hfit : st.toNat + 128 ≤ 2 ^ 32)
    (hw : VG.Proof.Poly1305.X86.sR st ∈ s.wr) :
    WP isa (.block save) s fun s' => ∃ f, VG.Proof.Poly1305.X86.After st s s' f [.eax, .edi] ∧ s'.gpr .edi = st ∧
      (∀ k, k < 29 → k ≠ 5 → f k = VG.Proof.Poly1305.X86.words s.mem st k) ∧ VG.Proof.Poly1305.X86.SavedIn s f := by
  have hc : ∀ d, d + 4 ≤ 128 → InRegions s.wr (addr st d) 4 := fun d hd =>
    ⟨_, hw, VG.Proof.Poly1305.X86.sR_contains hfit hd (by decide)⟩
  rw [VG.Proof.Poly1305.X86.save_eq]
  refine VG.Proof.Poly1305.X86.wp_movm (a := addr (s.gpr .esp) 4) (VG.Proof.Poly1305.X86.ea_at _ _ _) harg fun s₁ u₁ _ => ?_
  have e₁ : s₁.gpr .eax = st := by rw [u₁.gpr, hst]
  refine VG.Proof.Poly1305.X86.wp_store (a := addr st (4 * 29)) (by rw [VG.Proof.Poly1305.X86.ea_at, e₁]) (by rw [u₁.wr]; exact hc _ (by decide))
    fun s₂ u₂ => ?_
  refine VG.Proof.Poly1305.X86.wp_store (a := addr st (4 * 30)) (by rw [VG.Proof.Poly1305.X86.ea_at, u₂.gpr, e₁])
    (by rw [u₂.wr, u₁.wr]; exact hc _ (by decide)) fun s₃ u₃ => ?_
  refine VG.Proof.Poly1305.X86.wp_store (a := addr st (4 * 31)) (by rw [VG.Proof.Poly1305.X86.ea_at, u₃.gpr, u₂.gpr, e₁])
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact hc _ (by decide)) fun s₄ u₄ => ?_
  refine VG.Proof.Poly1305.X86.wp_store (a := addr st (4 * 5)) (by rw [VG.Proof.Poly1305.X86.ea_at, u₄.gpr, u₃.gpr, u₂.gpr, e₁])
    (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hc _ (by decide)) fun s₅ u₅ => ?_
  refine VG.Proof.Poly1305.X86.wp_mov fun s₆ u₆ _ => WP.block_nil ⟨VG.Proof.Poly1305.X86.upd (VG.Proof.Poly1305.X86.upd (VG.Proof.Poly1305.X86.upd (VG.Proof.Poly1305.X86.upd (VG.Proof.Poly1305.X86.words s.mem st) 29 (VG.Proof.Poly1305.X86.v s .ebx)) 30
    (VG.Proof.Poly1305.X86.v s .esi)) 31 (VG.Proof.Poly1305.X86.v s .edi)) 5 (VG.Proof.Poly1305.X86.v s .ebp), ⟨?_, ?_, fun r hr => ?_, ?_, ?_⟩, ?_, fun k hk hk5 => ?_, ?_⟩
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₄.gpr, u₃.gpr, u₂.gpr, u₁.mem, u₁.other .ebx (by decide),
      u₁.other .esi (by decide), u₁.other .edi (by decide), u₁.other .ebp (by decide)]
    exact ((((VG.Proof.Poly1305.X86.words_ok s.mem st).write hfit (j := 29) (by decide) _).write hfit (j := 30) (by decide)
      _).write hfit (j := 31) (by decide) _).write hfit (j := 5) (by decide) _
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    exact VG.Proof.Poly1305.X86.frame_write (VG.Proof.Poly1305.X86.frame_write (VG.Proof.Poly1305.X86.frame_write (VG.Proof.Poly1305.X86.frame_write (Frame.refl _ _) hfit (by decide) _) hfit
      (by decide) _) hfit (by decide) _) hfit (by decide) _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₆.other r hr.2, u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, u₁.other r hr.1]
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₆.gpr, u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, e₁]
  · simp only [VG.Proof.Poly1305.X86.upd]
    rw [ite_eq_right (by omega_using [hk5]), ite_eq_right (by omega_using [hk]), ite_eq_right (by omega_using [hk]),
      ite_eq_right (by omega_using [hk])]
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [↓reduceIte, Nat.reduceEqDiff, VG.Proof.Poly1305.X86.upd]


theorem and0_toNat (x : BitVec 32) : (x &&& 0x0fffffff).toNat = x.toNat &&& 0x0fffffff := by
  rw [BitVec.toNat_and]; rfl

theorem and1_toNat (x : BitVec 32) : (x &&& 0x0ffffffc).toNat = x.toNat &&& 0x0ffffffc := by
  rw [BitVec.toNat_and]; rfl

/-- `r0` clamped. -/
theorem clamp0_ok {st : BitVec 32} {s : State} (hc : VG.Proof.Poly1305.X86.Ctx st s) {f : Nat → Nat} (hw : VG.Proof.Poly1305.X86.Words s.mem st f) :
    WP isa (.block clamp0) s fun s' => VG.Proof.Poly1305.X86.After st s s' (VG.Proof.Poly1305.X86.upd f 18 (f 6 &&& 0x0fffffff)) [.eax] := by
  have hfit := hc.fit
  refine VG.Proof.Poly1305.X86.wp_movm (a := addr st (4 * 6)) (by rw [VG.Proof.Poly1305.X86.ea_at, hc.edi]) (hc.inRW (by decide) (by decide))
    fun s₁ u₁ _ => VG.Proof.Poly1305.X86.wp_andx (VG.Proof.Poly1305.X86.readSrc_imm _ _) fun s₂ u₂ => ?_
  have edi₂ : s₂.gpr .edi = st := by rw [u₂.other .edi (by decide), u₁.other .edi (by decide), hc.edi]
  refine VG.Proof.Poly1305.X86.wp_store (a := addr st (4 * 18)) (by rw [VG.Proof.Poly1305.X86.ea_at, edi₂]; rfl)
    (by rw [u₂.wr, u₁.wr]; exact hc.inW (by decide) (by decide))
    fun s₃ u₃ => WP.block_nil ⟨?_, ?_, fun r hr => ?_, ?_, ?_⟩
  · rw [u₃.mem, u₂.mem, u₁.mem, u₂.gpr, u₁.gpr]
    refine (hw.write hfit (by decide) _).congr fun k _ => ?_
    simp only [VG.Proof.Poly1305.X86.upd]
    split
    · rw [VG.Proof.Poly1305.X86.and0_toNat, hw.readW (k := 6) (by decide)]
    · rfl
  · rw [u₃.mem, u₂.mem, u₁.mem]; exact VG.Proof.Poly1305.X86.frame_write (Frame.refl _ _) hfit (by decide) _
  · simp only [List.mem_singleton] at hr; rw [u₃.gpr, u₂.other r hr, u₁.other r hr]
  · rw [u₃.rd, u₂.rd, u₁.rd]
  · rw [u₃.wr, u₂.wr, u₁.wr]

/-- `rj` clamped and `sj = rj + rj / 4`, for `j = 1, 2, 3`. -/
theorem clampS_ok {st : BitVec 32} {s : State} (hc : VG.Proof.Poly1305.X86.Ctx st s) {f : Nat → Nat} (hw : VG.Proof.Poly1305.X86.Words s.mem st f)
    {j : Nat} (hj : 1 ≤ j ∧ j ≤ 3) :
    WP isa (.block (clampS j)) s fun s' => VG.Proof.Poly1305.X86.After st s s' (VG.Proof.Poly1305.X86.upd (VG.Proof.Poly1305.X86.upd f (18 + j) (f (6 + j) &&& 0x0ffffffc))
      (21 + j) ((f (6 + j) &&& 0x0ffffffc) + (f (6 + j) &&& 0x0ffffffc) / 4)) [.eax, .ecx] := by
  have hfit := hc.fit
  have hr : f (6 + j) &&& 0x0ffffffc < 2 ^ 28 := VG.Proof.Poly1305.X86.mask1_lt _
  refine VG.Proof.Poly1305.X86.wp_movm (a := addr st (4 * (6 + j))) (by rw [VG.Proof.Poly1305.X86.ea_at, hc.edi]; congr 1; omega_using [])
    (hc.inRW (by omega_using [hj]) (by decide)) fun s₁ u₁ _ => VG.Proof.Poly1305.X86.wp_andx (VG.Proof.Poly1305.X86.readSrc_imm _ _) fun s₂ u₂ => ?_
  have e₂ : (s₂.gpr .eax).toNat = f (6 + j) &&& 0x0ffffffc := by
    rw [u₂.gpr, u₁.gpr, VG.Proof.Poly1305.X86.and1_toNat, hw.readW (k := 6 + j) (by omega_using [hj])]
  have edi₂ : s₂.gpr .edi = st := by rw [u₂.other _ (by decide), u₁.other _ (by decide), hc.edi]
  refine VG.Proof.Poly1305.X86.wp_store (a := addr st (4 * (18 + j))) (by rw [VG.Proof.Poly1305.X86.ea_at, edi₂]; simp only [rOff]; congr 1; omega_using [])
    (by rw [u₂.wr, u₁.wr]; exact hc.inW (by omega_using [hj]) (by decide)) fun s₃ u₃ => ?_
  refine VG.Proof.Poly1305.X86.wp_mov fun s₄ u₄ _ => VG.Proof.Poly1305.X86.wp_shr (by decide) fun s₅ u₅ => VG.Proof.Poly1305.X86.wp_addx (VG.Proof.Poly1305.X86.readSrc_reg _ _) fun s₆ u₆ _ => ?_
  have e₆ : (s₆.gpr .eax).toNat = (f (6 + j) &&& 0x0ffffffc) + (f (6 + j) &&& 0x0ffffffc) / 4 := by
    rw [u₆.gpr, u₅.other .eax (by decide), u₅.gpr, u₄.gpr, u₄.other .eax (by decide), u₃.gpr,
      BitVec.toNat_add, VG.Proof.Poly1305.X86.shr2_toNat, e₂]
    omega_using [hr, e₂]
  have edi₆ : s₆.gpr .edi = st := by
    rw [u₆.other .edi (by decide), u₅.other .edi (by decide), u₄.other .edi (by decide), u₃.gpr, edi₂]
  refine VG.Proof.Poly1305.X86.wp_store (a := addr st (4 * (21 + j))) (by rw [VG.Proof.Poly1305.X86.ea_at, edi₆]; simp only [sOff]; congr 1; omega_using [])
    (by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hc.inW (by omega_using [hj]) (by decide))
    fun s₇ u₇ => WP.block_nil ⟨?_, ?_, fun r hr => ?_, ?_, ?_⟩
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    refine ((hw.write hfit (j := 18 + j) (by omega_using [hj]) _).write hfit (j := 21 + j) (by omega_using [hj]) _).congr
      fun k _ => ?_
    rw [e₂, e₆]
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    exact VG.Proof.Poly1305.X86.frame_write (VG.Proof.Poly1305.X86.frame_write (Frame.refl _ _) hfit (by omega_using [hj]) _) hfit (by omega_using [hj]) _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₇.gpr, u₆.other r hr.1, u₅.other r hr.2, u₄.other r hr.2, u₃.gpr, u₂.other r hr.1,
      u₁.other r hr.1]
  · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]


theorem setup_eq : setup = save ++ (clamp0 ++ (clampS 1 ++ (clampS 2 ++ clampS 3))) := by
  simp only [setup, List.append_assoc]

section
variable (m : Mem) (st : BitVec 32)
/-- The clamped `r0`, and `rj = 4 qj`, of the key in the state's words. -/
def r0v : Nat := VG.Proof.Poly1305.X86.words m st 6 &&& 0x0fffffff
def qv (j : Nat) : Nat := (VG.Proof.Poly1305.X86.words m st (6 + j) &&& 0x0ffffffc) / 4
end

theorem coef_facts {x : Nat} : x &&& 0x0ffffffc = 4 * ((x &&& 0x0ffffffc) / 4) ∧
    (x &&& 0x0ffffffc) + (x &&& 0x0ffffffc) / 4 = 5 * ((x &&& 0x0ffffffc) / 4) ∧
    (x &&& 0x0ffffffc) / 4 < 2 ^ 26 := by
  have h1 := VG.Proof.Poly1305.X86.mask1_mod x; have h2 := VG.Proof.Poly1305.X86.mask1_lt x
  refine ⟨by omega_using [h1], by omega_using [h1], by omega_using [h1, h2]⟩

/-- Everything each function but `init` does first: the state at `[esp + 4]`
into `edi`, the callee-saved registers saved in it, and the clamped `r`
and `sj` in its words. -/
theorem setup_ok {s₀ : State} {st : BitVec 32} (hst : s₀.mem.readW (addr (s₀.gpr .esp) 4) 32 = st)
    (harg : InRegions (s₀.rd ++ s₀.wr) (addr (s₀.gpr .esp) 4) 4) (hfit : st.toNat + 128 ≤ 2 ^ 32)
    (hw : VG.Proof.Poly1305.X86.sR st ∈ s₀.wr) :
    WP isa (.block setup) s₀ fun s => ∃ F, VG.Proof.Poly1305.X86.After st s₀ s F [.eax, .ecx, .edi] ∧ VG.Proof.Poly1305.X86.Ctx st s ∧
      (∀ k, (k < 18 ∧ k ≠ 5) ∨ (25 ≤ k ∧ k < 29) → F k = VG.Proof.Poly1305.X86.words s₀.mem st k) ∧ VG.Proof.Poly1305.X86.SavedIn s₀ F ∧
      VG.Proof.Poly1305.X86.Coefs F (VG.Proof.Poly1305.X86.r0v s₀.mem st) (VG.Proof.Poly1305.X86.qv s₀.mem st 1) (VG.Proof.Poly1305.X86.qv s₀.mem st 2) (VG.Proof.Poly1305.X86.qv s₀.mem st 3) := by
  rw [VG.Proof.Poly1305.X86.setup_eq]
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86.save_ok hst harg hfit hw) fun s₁ ⟨f₁, A₁, e₁, h₁, sv₁⟩ => ?_)
  have c₁ : VG.Proof.Poly1305.X86.Ctx st s₁ := ⟨e₁, hfit, A₁.wr ▸ hw⟩
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86.clamp0_ok c₁ A₁.words) fun s₂ A₂ => ?_)
  have c₂ := A₂.ctx c₁
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86.clampS_ok c₂ A₂.words (j := 1) (by decide)) fun s₃ A₃ => ?_)
  have c₃ := A₃.ctx c₂
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86.clampS_ok c₃ A₃.words (j := 2) (by decide)) fun s₄ A₄ => ?_)
  have c₄ := A₄.ctx c₃
  refine WP.mono (VG.Proof.Poly1305.X86.clampS_ok c₄ A₄.words (j := 3) (by decide)) fun s₅ A₅ =>
    ⟨_, (A₁.trans (A₂.trans (A₃.trans (A₄.trans A₅)))).mono, A₅.ctx c₄, fun k hk => ?_, ?_, ?_⟩
  · simp only [VG.Proof.Poly1305.X86.upd]
    rw [ite_eq_right (by omega_using [hk]), ite_eq_right (by omega_using [hk]), ite_eq_right (by omega_using [hk]), ite_eq_right (by omega_using [hk]),
      ite_eq_right (by omega_using [hk]), ite_eq_right (by omega_using [hk]), ite_eq_right (by omega_using [hk]), h₁ k (by omega_using [hk]) (by omega_using [hk])]
  · obtain ⟨b1, b2, b3, b4⟩ := sv₁
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp (config := {decide := true}) only [VG.Proof.Poly1305.X86.upd, ite_false] <;>
      assumption
  · have w6 : f₁ 6 = VG.Proof.Poly1305.X86.words s₀.mem st 6 := h₁ 6 (by decide) (by decide)
    have w7 : f₁ 7 = VG.Proof.Poly1305.X86.words s₀.mem st 7 := h₁ 7 (by decide) (by decide)
    have w8 : f₁ 8 = VG.Proof.Poly1305.X86.words s₀.mem st 8 := h₁ 8 (by decide) (by decide)
    have w9 : f₁ 9 = VG.Proof.Poly1305.X86.words s₀.mem st 9 := h₁ 9 (by decide) (by decide)
    obtain ⟨a1, a2, a3⟩ := VG.Proof.Poly1305.X86.coef_facts (x := VG.Proof.Poly1305.X86.words s₀.mem st 7)
    obtain ⟨b1, b2, b3⟩ := VG.Proof.Poly1305.X86.coef_facts (x := VG.Proof.Poly1305.X86.words s₀.mem st 8)
    obtain ⟨d1, d2, d3⟩ := VG.Proof.Poly1305.X86.coef_facts (x := VG.Proof.Poly1305.X86.words s₀.mem st 9)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, VG.Proof.Poly1305.X86.mask0_lt _, a3, b3, d3⟩ <;>
      simp (config := {decide := true}) only [VG.Proof.Poly1305.X86.upd, ite_true, ite_false, w6, w7, w8, w9, VG.Proof.Poly1305.X86.r0v, VG.Proof.Poly1305.X86.qv,
        Nat.reduceAdd]
    exacts [a1, b1, d1, a2, b2, d2]

end VG.Proof.Poly1305.X86

end

section

/-!
# Poly1305 on x86 (32-bit): straight-line code runs, whatever the values

The lemmas on absorbing a block and the final reduction (above) state what the
code computes where the numbers are within their bounds (as they are when the
state represents a message). Whatever the values, the code runs without a
fault: it accesses only the state (at `edi`) and the block (at `esi`), stores
only some words of the state and writes only some registers. `okList` checks
this of a block of code, by evaluation, and `okList_ok` proves it.
-/

namespace VG.Proof.Poly1305.X86

open VG VG.X86 VG.Impl.Poly1305.X86

/-- A memory operand the code may read: a word of the state or of the block. -/
def memOk (blk : Bool) (m : MemOp) : Bool :=
  (m.base == .edi && m.disp + 4 ≤ 128) || (blk && m.base == .esi && m.disp + 4 ≤ 16)

def srcOk (blk : Bool) : Src → Bool
  | .mem m => VG.Proof.Poly1305.X86.memOk blk m
  | _ => true

/-- Whether an instruction only reads the state or the block, stores only
the words `S` of the state and writes only the registers `rs`, with `c`
whether CF is defined; and then whether CF is defined afterwards. -/
def okStep (blk : Bool) (rs : List Reg) (S : List Nat) (c : Bool) : Instr → Option Bool
  | .mov d src => if rs.contains d && VG.Proof.Poly1305.X86.srcOk blk src then some c else none
  | .store m _ =>
    if m.base == .edi && m.disp % 4 == 0 && S.contains (m.disp / 4) && m.disp + 4 ≤ 128 then some c
    else none
  | .alu op d src =>
    if rs.contains d && VG.Proof.Poly1305.X86.srcOk blk src && (!Taint.usesCarry op || c) then some true else none
  | .shift _ d n => if rs.contains d && 1 ≤ n && n ≤ 31 then some true else none
  | .mul _ => if rs.contains .eax && rs.contains .edx then some true else none
  | _ => none

def okList (blk : Bool) (rs : List Reg) (S : List Nat) : Bool → List Instr → Bool
  | _, [] => true
  | c, i :: is => match VG.Proof.Poly1305.X86.okStep blk rs S c i with
    | some c' => VG.Proof.Poly1305.X86.okList blk rs S c' is
    | none => false

/-- What an instruction or block that `okStep` accepts leaves. -/
structure Safe (st : BitVec 32) (rs : List Reg) (S : List Nat) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ rs → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [VG.Proof.Poly1305.X86.sR st] s.mem s'.mem
  same : ∀ k < 32, k ∉ S → VG.Proof.Poly1305.X86.wv s'.mem st (4 * k) = VG.Proof.Poly1305.X86.wv s.mem st (4 * k)

theorem Safe.refl (st : BitVec 32) (rs : List Reg) (S : List Nat) (s : State) : VG.Proof.Poly1305.X86.Safe st rs S s s :=
  ⟨fun _ _ => rfl, rfl, rfl, Frame.refl _ _, fun _ _ _ => rfl⟩

theorem Safe.trans {st : BitVec 32} {rs : List Reg} {S : List Nat} {s₁ s₂ s₃ : State}
    (h₁ : VG.Proof.Poly1305.X86.Safe st rs S s₁ s₂) (h₂ : VG.Proof.Poly1305.X86.Safe st rs S s₂ s₃) : VG.Proof.Poly1305.X86.Safe st rs S s₁ s₃ :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr,
    h₁.frame.trans h₂.frame, fun k hk hS => (h₂.same k hk hS).trans (h₁.same k hk hS)⟩

/-- The block's words may be read. -/
def BlkIn (s : State) : Prop := ∀ d, d + 4 ≤ 16 → InRegions (s.rd ++ s.wr) (addr (s.gpr .esi) d) 4

theorem readSrc_ok {st : BitVec 32} {s : State} {blk : Bool} (hc : VG.Proof.Poly1305.X86.Ctx st s) (hb : blk = true → VG.Proof.Poly1305.X86.BlkIn s)
    {src : Src} (h : VG.Proof.Poly1305.X86.srcOk blk src = true) : ∃ x, readSrc s src = some x := by
  cases src with
  | reg r => exact ⟨_, rfl⟩
  | imm w => exact ⟨_, rfl⟩
  | mem m =>
    have ea : s.ea m = addr (s.gpr m.base) m.disp := rfl
    simp only [VG.Proof.Poly1305.X86.srcOk, VG.Proof.Poly1305.X86.memOk, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    rcases h with ⟨hb', hd⟩ | ⟨⟨hbk, hb'⟩, hd⟩
    · rw [hb', hc.edi] at ea
      exact ⟨_, VG.Proof.Poly1305.X86.readSrc_mem ea (hc.inRW hd (by decide))⟩
    · rw [hb'] at ea
      exact ⟨_, VG.Proof.Poly1305.X86.readSrc_mem ea (hb hbk _ hd)⟩

/-- An instruction that writes at most the register `d`, and no memory. -/
theorem safe_dst {st : BitVec 32} {rs : List Reg} {S : List Nat} {i : Instr} {d : Reg}
    (hd : Taint.dst i = some d) (hdr : d ∈ rs) {s s' : State} (h : exec i s = some s') :
    VG.Proof.Poly1305.X86.Safe st rs S s s' := by
  obtain ⟨hw, hm, hg⟩ := Taint.exec_dst hd h
  refine ⟨fun r hr => hg r fun e => hr (e ▸ hdr), (exec_regions h).1, hw, ?_, fun _ _ _ => ?_⟩
  · rw [hm]; exact Frame.refl _ _
  · rw [hm]

theorem okStep_ok {st : BitVec 32} {blk : Bool} {rs : List Reg} {S : List Nat} {c c' : Bool} {i : Instr}
    (h : VG.Proof.Poly1305.X86.okStep blk rs S c i = some c') {s : State} (hc : VG.Proof.Poly1305.X86.Ctx st s) (hb : blk = true → VG.Proof.Poly1305.X86.BlkIn s)
    (hcf : c = true → s.cf.isSome) :
    ∃ s', exec i s = some s' ∧ VG.Proof.Poly1305.X86.Safe st rs S s s' ∧ (c' = true → s'.cf.isSome) := by
  have hfit := hc.fit
  cases i with
  | mov d src =>
    simp only [VG.Proof.Poly1305.X86.okStep, Bool.and_eq_true, List.contains_iff_mem] at h
    split at h <;> [skip; cases h]
    rename_i hd
    obtain ⟨x, hx⟩ := VG.Proof.Poly1305.X86.readSrc_ok hc hb hd.2
    have he : exec (.mov d src) s = some (s.setReg d x) := by simp only [exec, hx, Option.map_some]
    refine ⟨_, he, VG.Proof.Poly1305.X86.safe_dst rfl hd.1 he, ?_⟩
    simp only [Option.some.injEq] at h
    subst h; exact hcf
  | store m r =>
    simp only [VG.Proof.Poly1305.X86.okStep, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, decide_eq_true_eq] at h
    split at h <;> [skip; cases h]
    rename_i hm
    obtain ⟨⟨⟨hb', h4⟩, hS⟩, hd⟩ := hm
    have ea : s.ea m = addr (s.gpr m.base) m.disp := rfl
    rw [hb', hc.edi, show m.disp = 4 * (m.disp / 4) by omega_using [h4]] at ea
    refine ⟨{ s with mem := s.mem.writeW (addr st (4 * (m.disp / 4))) (s.gpr r) }, ?_, ⟨fun _ _ => rfl,
      rfl, rfl, VG.Proof.Poly1305.X86.frame_write (Frame.refl _ _) hfit (by omega_using [hd, h4]) _, fun k hk hkS => ?_⟩, ?_⟩
    · simp only [exec, State.store32, ea, hc.inW (by omega_using [hd, h4] : 4 * (m.disp / 4) + 4 ≤ 128) (by decide),
        ite_true]
    · show VG.Proof.Poly1305.X86.wv (s.mem.writeW _ _) st (4 * k) = _
      have : k ≠ m.disp / 4 := fun e => hkS (e ▸ hS)
      rw [VG.Proof.Poly1305.X86.wv, VG.Proof.Poly1305.X86.wd_write_ne _ _ (by omega_using [hfit, hk]) (by omega_using [hfit, hd, h4]) (by omega_using [this])]
    · simp only [Option.some.injEq] at h
      subst h; exact hcf
  | alu op d src =>
    simp only [VG.Proof.Poly1305.X86.okStep, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.contains_iff_mem] at h
    split at h <;> [skip; cases h]
    rename_i hd
    obtain ⟨⟨hdr, hsrc⟩, hcarry⟩ := hd
    obtain ⟨x, hx⟩ := VG.Proof.Poly1305.X86.readSrc_ok hc hb hsrc
    obtain ⟨o, ho⟩ : ∃ o, Taint.aluOut op (s.gpr d) x s.cf = some o := by
      cases op <;> simp only [Taint.aluOut] <;>
        first
        | exact ⟨_, rfl⟩
        | (obtain ⟨c₀, hc₀⟩ := Option.isSome_iff_exists.mp (hcf (hcarry.resolve_left (by decide)))
           rw [hc₀]; exact ⟨_, rfl⟩)
    obtain ⟨r, co, oo⟩ := o
    have he : exec (.alu op d src) s = some (if Taint.writes op then (arithFlags s r co oo).setReg d r
        else arithFlags s r co oo) := by
      simp only [exec, Taint.execAlu_eq, hx, Option.bind_some, ho, Option.map_some]
    refine ⟨_, he, VG.Proof.Poly1305.X86.safe_dst rfl hdr he, fun _ => ?_⟩
    split <;> rfl
  | shift op d n =>
    simp only [VG.Proof.Poly1305.X86.okStep, Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq] at h
    split at h <;> [skip; cases h]
    rename_i hd
    obtain ⟨⟨hdr, h1⟩, h2⟩ := hd
    have hn : 1 ≤ n ∧ n ≤ 31 := ⟨h1, h2⟩
    obtain ⟨s', he⟩ : ∃ s', exec (.shift op d n) s = some s' := by
      cases op <;> exact ⟨_, by simp only [exec, execShift, hn, and_self, ite_true]; rfl⟩
    refine ⟨s', he, VG.Proof.Poly1305.X86.safe_dst rfl hdr he, fun _ => ?_⟩
    cases op <;> simp only [exec, execShift, hn, and_self, ite_true, Option.some.injEq] at he <;>
      subst he <;> rfl
  | mul q =>
    simp only [VG.Proof.Poly1305.X86.okStep, Bool.and_eq_true, List.contains_iff_mem] at h
    split at h <;> [skip; cases h]
    rename_i hd
    refine ⟨execMul q s, rfl, ⟨fun r hr => Taint.execMul_gpr q s (fun e => hr (e ▸ hd.1))
      (fun e => hr (e ▸ hd.2)), rfl, rfl, Frame.refl _ _, fun _ _ _ => rfl⟩, fun _ => rfl⟩
  | bswap | movzx8 | store8 | push | pop | alloc | free | movdquLoad | movdquStore | movqLoad | movqStore | xop | mop | mmxStore | mmxEnter | emms =>
    simp only [VG.Proof.Poly1305.X86.okStep, reduceCtorEq] at h

/-- A block that `okList` accepts runs, whatever the values. -/
theorem okList_ok {st : BitVec 32} {blk : Bool} {rs : List Reg} {S : List Nat}
    (hrs : Reg.edi ∉ rs ∧ Reg.esi ∉ rs) :
    ∀ (is : List Instr) (c : Bool) (s : State), VG.Proof.Poly1305.X86.okList blk rs S c is = true → VG.Proof.Poly1305.X86.Ctx st s →
      (blk = true → VG.Proof.Poly1305.X86.BlkIn s) →
      (c = true → s.cf.isSome) → WP isa (.block is) s (VG.Proof.Poly1305.X86.Safe st rs S s) := by
  intro is
  induction is with
  | nil => intro _ s _ _ _ _; exact WP.block_nil (Safe.refl _ _ _ _)
  | cons i is ih =>
    intro c s h hc hb hcf
    simp only [VG.Proof.Poly1305.X86.okList] at h
    split at h <;> [skip; cases h]
    rename_i c' hi
    obtain ⟨s₁, he, hs, hcf₁⟩ := VG.Proof.Poly1305.X86.okStep_ok hi hc hb hcf
    refine WP.cons he (WP.mono (ih c' s₁ h (hc.keep (hs.gpr _ hrs.1) hs.wr) ?_ hcf₁)
      fun s₂ h₂ => hs.trans h₂)
    intro hbk d hd
    rw [hs.rd, hs.wr, hs.gpr _ hrs.2]; exact hb hbk d hd

/-- The words a `Safe` block leaves. -/
theorem Safe.after {st : BitVec 32} {rs : List Reg} {S : List Nat} {s s' : State}
    (h : VG.Proof.Poly1305.X86.Safe st rs S s s') : VG.Proof.Poly1305.X86.After st s s' (VG.Proof.Poly1305.X86.words s'.mem st) rs :=
  ⟨VG.Proof.Poly1305.X86.words_ok _ _, h.frame, h.gpr, h.rd, h.wr⟩

/-- A run of `c` satisfies `Q₁`, and `Q₂` where `C` holds (runs are deterministic). -/
theorem WP.cond {c : Prog isa} {s : State} {Q₁ Q₂ : State → Prop} {C : Prop}
    (h₁ : WP isa c s Q₁) (h₂ : C → WP isa c s Q₂) : WP isa c s fun s' => Q₁ s' ∧ (C → Q₂ s') := by
  obtain ⟨t, s', he, hq⟩ := h₁
  refine ⟨t, s', he, hq, fun hC => ?_⟩
  obtain ⟨t₂, s₂, he₂, hq₂⟩ := h₂ hC
  rw [(Exec.det he he₂).2]; exact hq₂

theorem words_eq {m : Mem} {st : BitVec 32} {g : Nat → Nat} (hw : VG.Proof.Poly1305.X86.Words m st g) {k : Nat}
    (hk : k < 32) : VG.Proof.Poly1305.X86.words m st k = g k := hw k hk

end VG.Proof.Poly1305.X86

end

/-!
# Poly1305 on x86 (32-bit): the parts of each function, whatever the values

Absorbing a block and the final reduction run whatever the values (`Safe`),
and compute what the lemmas on them (above) say where the numbers are within
their bounds.
-/

namespace VG.Proof.Poly1305.X86

open VG VG.X86 VG.Impl.Poly1305.X86
open VG.Spec.Poly1305 (P)

/-- The registers `absorb` writes, and the words of the state it stores. -/
abbrev aRegs : List Reg := [.eax, .ebx, .ecx, .edx, .ebp]
abbrev hS : List Nat := [0, 1, 2, 3, 4, 25, 26, 27, 28]

/-- The value of the block at `bp`, from its four words, and `pad · 2¹²⁸`. -/
abbrev blkv (m : Mem) (bp : BitVec 32) (pad : Nat) : Nat :=
  VG.Proof.Poly1305.X86.wv m bp 0 + 2 ^ 32 * VG.Proof.Poly1305.X86.wv m bp 4 + 2 ^ 64 * VG.Proof.Poly1305.X86.wv m bp 8 + 2 ^ 96 * VG.Proof.Poly1305.X86.wv m bp 12 + 2 ^ 128 * pad

theorem absorb_okList (pad : BitVec 32) : VG.Proof.Poly1305.X86.okList true VG.Proof.Poly1305.X86.aRegs VG.Proof.Poly1305.X86.hS false (absorb pad) = true := rfl

theorem absorbBuf_okList (pad : BitVec 32) : VG.Proof.Poly1305.X86.okList false VG.Proof.Poly1305.X86.aRegs VG.Proof.Poly1305.X86.hS false (absorbAt .edi 56 pad) = true :=
  rfl

/-- Absorbing the block at `b + d` (at `bp`, outside the state or in its
buffer): it runs, and where `C` gives the bounds, the new `h` is congruent to
`(h + m + pad · 2¹²⁸) r` modulo `p`. -/
theorem absorbAtFull_ok {st bp : BitVec 32} {s : State} (hc : VG.Proof.Poly1305.X86.Ctx st s) {b : Reg} {d : Nat} {blk : Bool}
    {pad : BitVec 32} (hok : VG.Proof.Poly1305.X86.okList blk VG.Proof.Poly1305.X86.aRegs VG.Proof.Poly1305.X86.hS false (absorbAt b d pad) = true)
    (hb : blk = true → VG.Proof.Poly1305.X86.BlkIn s) (hbase : b ≠ .eax)
    (hea : ∀ k < 4, addr (s.gpr b) (d + 4 * k) = addr bp (4 * k))
    (hrd : ∀ k < 4, InRegions (s.rd ++ s.wr) (addr bp (4 * k)) 4)
    (hd : ∀ k < 4, (VG.Proof.Poly1305.X86.sub bp (4 * k) 4).Disjoint (VG.Proof.Poly1305.X86.sR st) ∨ addr bp (4 * k) = addr st (4 * (14 + k)))
    (hpad : pad.toNat ≤ 1) {C : Prop} {r0 q1 q2 q3 : Nat}
    (hC : C → VG.Proof.Poly1305.X86.Coefs (VG.Proof.Poly1305.X86.words s.mem st) r0 q1 q2 q3 ∧ VG.Proof.Poly1305.X86.words s.mem st 4 ≤ 4) :
    WP isa (.block (absorbAt b d pad)) s fun s' => VG.Proof.Poly1305.X86.Safe st VG.Proof.Poly1305.X86.aRegs VG.Proof.Poly1305.X86.hS s s' ∧ (C → VG.Proof.Poly1305.X86.words s'.mem st 4 ≤ 4 ∧
      VG.Proof.Poly1305.X86.hw5 (VG.Proof.Poly1305.X86.words s'.mem st) % P = ((VG.Proof.Poly1305.X86.hw5 (VG.Proof.Poly1305.X86.words s.mem st) + VG.Proof.Poly1305.X86.blkv s.mem bp pad.toNat) * VG.Proof.Poly1305.X86.rval r0 q1 q2 q3) % P) := by
  refine WP.cond (VG.Proof.Poly1305.X86.okList_ok ⟨by decide, by decide⟩ _ false s hok hc hb
    (fun h => absurd h (by decide))) fun hC' => ?_
  obtain ⟨hco, h4⟩ := hC hC'
  refine WP.mono (VG.Proof.Poly1305.X86.absorb_ok ⟨hc, VG.Proof.Poly1305.X86.words_ok _ _, hbase, hea, hrd, hd⟩ hco h4 pad hpad)
    fun s' ⟨g, A, _, _, hv, hg4⟩ => ?_
  have e : ∀ k < 32, VG.Proof.Poly1305.X86.words s'.mem st k = g k := fun k hk => A.words k hk
  simp only [VG.Proof.Poly1305.X86.hw5, e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide), e 4 (by decide)]
  exact ⟨hg4, hv⟩

/-- Absorbing the block at `esi`, outside the state. -/
theorem absorbFull_ok {st : BitVec 32} {s : State} (hc : VG.Proof.Poly1305.X86.Ctx st s) (hb : VG.Proof.Poly1305.X86.BlkIn s)
    (hd : ∀ k < 4, (VG.Proof.Poly1305.X86.sub (s.gpr .esi) (4 * k) 4).Disjoint (VG.Proof.Poly1305.X86.sR st)) (pad : BitVec 32)
    (hpad : pad.toNat ≤ 1) {C : Prop} {r0 q1 q2 q3 : Nat}
    (hC : C → VG.Proof.Poly1305.X86.Coefs (VG.Proof.Poly1305.X86.words s.mem st) r0 q1 q2 q3 ∧ VG.Proof.Poly1305.X86.words s.mem st 4 ≤ 4) :
    WP isa (.block (absorb pad)) s fun s' => VG.Proof.Poly1305.X86.Safe st VG.Proof.Poly1305.X86.aRegs VG.Proof.Poly1305.X86.hS s s' ∧ (C → VG.Proof.Poly1305.X86.words s'.mem st 4 ≤ 4 ∧
      VG.Proof.Poly1305.X86.hw5 (VG.Proof.Poly1305.X86.words s'.mem st) % P =
        ((VG.Proof.Poly1305.X86.hw5 (VG.Proof.Poly1305.X86.words s.mem st) + VG.Proof.Poly1305.X86.blkv s.mem (s.gpr .esi) pad.toNat) * VG.Proof.Poly1305.X86.rval r0 q1 q2 q3) % P) :=
  VG.Proof.Poly1305.X86.absorbAtFull_ok hc (VG.Proof.Poly1305.X86.absorb_okList pad) (fun _ => hb) (by decide) (fun k _ => by rw [Nat.zero_add])
    (fun k _ => hb (4 * k) (by omega)) (fun k hk => .inl (hd k hk)) hpad hC

/-- The registers `reduce` writes. -/
abbrev rRegs : List Reg := [.eax, .ecx, .edx, .ebp]

theorem reduce_okList : VG.Proof.Poly1305.X86.okList false VG.Proof.Poly1305.X86.rRegs VG.Proof.Poly1305.X86.hS false reduce = true := by decide

/-- The final reduction: it runs, and where `h4 ≤ 4`, it leaves `h mod p`. -/
theorem reduceFull_ok {st : BitVec 32} {s : State} (hc : VG.Proof.Poly1305.X86.Ctx st s) :
    WP isa (.block reduce) s fun s' => VG.Proof.Poly1305.X86.Safe st VG.Proof.Poly1305.X86.rRegs VG.Proof.Poly1305.X86.hS s s' ∧ (VG.Proof.Poly1305.X86.words s.mem st 4 ≤ 4 →
      VG.Proof.Poly1305.X86.hw5 (VG.Proof.Poly1305.X86.words s'.mem st) = VG.Proof.Poly1305.X86.hw5 (VG.Proof.Poly1305.X86.words s.mem st) % P ∧ VG.Proof.Poly1305.X86.words s'.mem st 4 < 4) := by
  refine WP.cond (VG.Proof.Poly1305.X86.okList_ok ⟨by decide, by decide⟩ _ false s VG.Proof.Poly1305.X86.reduce_okList hc (fun h => absurd h (by decide))
    (fun h => absurd h (by decide))) fun h4 => ?_
  refine WP.mono (VG.Proof.Poly1305.X86.reduce_ok hc (VG.Proof.Poly1305.X86.words_ok _ _) h4) fun s' ⟨g, A, _, _, hv, hg4⟩ => ?_
  have e : ∀ k < 32, VG.Proof.Poly1305.X86.words s'.mem st k = g k := fun k hk => A.words k hk
  simp only [VG.Proof.Poly1305.X86.hw5, e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide), e 4 (by decide)]
  exact ⟨hv, hg4⟩

theorem restore_eq : restore = [.mov .eax (.reg .edi), .mov .ebx (.mem (at_ .eax 116)),
    .mov .esi (.mem (at_ .eax 120)), .mov .edi (.mem (at_ .eax 124)), .mov .ebp (.mem (at_ .eax 20)),
    .mov .ecx (.imm 0), .store (at_ .eax 20) .ecx] :=
  rfl

/-- Restoring the callee-saved registers from the state, and zeroing the word
that held `ebp`. -/
theorem restore_ok {st : BitVec 32} {s : State} (hc : VG.Proof.Poly1305.X86.Ctx st s) :
    WP isa (.block restore) s fun s' =>
      VG.Proof.Poly1305.X86.v s' .ebx = VG.Proof.Poly1305.X86.words s.mem st 29 ∧ VG.Proof.Poly1305.X86.v s' .esi = VG.Proof.Poly1305.X86.words s.mem st 30 ∧ VG.Proof.Poly1305.X86.v s' .edi = VG.Proof.Poly1305.X86.words s.mem st 31 ∧
      VG.Proof.Poly1305.X86.v s' .ebp = VG.Proof.Poly1305.X86.words s.mem st 5 ∧ s'.gpr .esp = s.gpr .esp ∧
      VG.Proof.Poly1305.X86.After st s s' (VG.Proof.Poly1305.X86.upd (VG.Proof.Poly1305.X86.words s.mem st) 5 0) [.eax, .ebx, .ecx, .esi, .edi, .ebp] := by
  have hfit := hc.fit
  rw [VG.Proof.Poly1305.X86.restore_eq]
  refine VG.Proof.Poly1305.X86.wp_mov fun s₁ u₁ _ => ?_
  have e₁ : s₁.gpr .eax = st := by rw [u₁.gpr, hc.edi]
  have c₁ : VG.Proof.Poly1305.X86.Ctx st s₁ := hc.keep (u₁.other _ (by decide)) u₁.wr
  refine VG.Proof.Poly1305.X86.wp_movm (a := addr st (4 * 29)) (by rw [VG.Proof.Poly1305.X86.ea_at, e₁]) (c₁.inRW (by decide) (by decide))
    fun s₂ u₂ _ => ?_
  have e₂ : s₂.gpr .eax = st := by rw [u₂.other .eax (by decide), e₁]
  refine VG.Proof.Poly1305.X86.wp_movm (a := addr st (4 * 30)) (by rw [VG.Proof.Poly1305.X86.ea_at, e₂])
    (by rw [u₂.rd, u₂.wr]; exact c₁.inRW (by decide) (by decide)) fun s₃ u₃ _ => ?_
  have e₃ : s₃.gpr .eax = st := by rw [u₃.other .eax (by decide), e₂]
  refine VG.Proof.Poly1305.X86.wp_movm (a := addr st (4 * 31)) (by rw [VG.Proof.Poly1305.X86.ea_at, e₃])
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr]; exact c₁.inRW (by decide) (by decide)) fun s₄ u₄ _ => ?_
  have e₄ : s₄.gpr .eax = st := by rw [u₄.other .eax (by decide), e₃]
  have r₄ : InRegions (s₄.rd ++ s₄.wr) (addr st (4 * 5)) 4 := by
    rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr]; exact c₁.inRW (by decide) (by decide)
  refine VG.Proof.Poly1305.X86.wp_movm (a := addr st (4 * 5)) (by rw [VG.Proof.Poly1305.X86.ea_at, e₄]) r₄ fun s₅ u₅ _ => ?_
  refine VG.Proof.Poly1305.X86.wp_movi fun s₆ u₆ _ => ?_
  have e₆ : s₆.gpr .eax = st := by rw [u₆.other .eax (by decide), u₅.other .eax (by decide), e₄]
  have w₆ : VG.Proof.Poly1305.X86.sR st ∈ s₆.wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hc.wr
  refine VG.Proof.Poly1305.X86.wp_store (a := addr st (4 * 5)) (by rw [VG.Proof.Poly1305.X86.ea_at, e₆]) ⟨_, w₆, VG.Proof.Poly1305.X86.sR_contains hfit (by decide) (by decide)⟩
    fun s₇ u₇ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, fun r hr => ?_, ?_, ?_⟩⟩
  · simp only [VG.Proof.Poly1305.X86.v, VG.Proof.Poly1305.X86.words, VG.Proof.Poly1305.X86.wv, VG.Proof.Poly1305.X86.wd]
    rw [u₇.gpr, u₆.other .ebx (by decide), u₅.other .ebx (by decide), u₄.other .ebx (by decide),
      u₃.other .ebx (by decide), u₂.gpr, u₁.mem]
  · simp only [VG.Proof.Poly1305.X86.v, VG.Proof.Poly1305.X86.words, VG.Proof.Poly1305.X86.wv, VG.Proof.Poly1305.X86.wd]
    rw [u₇.gpr, u₆.other .esi (by decide), u₅.other .esi (by decide), u₄.other .esi (by decide), u₃.gpr,
      u₂.mem, u₁.mem]
  · simp only [VG.Proof.Poly1305.X86.v, VG.Proof.Poly1305.X86.words, VG.Proof.Poly1305.X86.wv, VG.Proof.Poly1305.X86.wd]
    rw [u₇.gpr, u₆.other .edi (by decide), u₅.other .edi (by decide), u₄.gpr, u₃.mem, u₂.mem, u₁.mem]
  · simp only [VG.Proof.Poly1305.X86.v, VG.Proof.Poly1305.X86.words, VG.Proof.Poly1305.X86.wv, VG.Proof.Poly1305.X86.wd]
    rw [u₇.gpr, u₆.other .ebp (by decide), u₅.gpr, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₇.gpr, u₆.other .esp (by decide), u₅.other .esp (by decide), u₄.other .esp (by decide),
      u₃.other .esp (by decide), u₂.other .esp (by decide), u₁.other .esp (by decide)]
  · rw [u₇.mem, u₆.gpr, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    exact (VG.Proof.Poly1305.X86.words_ok s.mem st).write hfit (j := 5) (by decide) 0
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    exact VG.Proof.Poly1305.X86.frame_write (Frame.refl _ _) hfit (by decide) _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₇.gpr, u₆.other r hr.2.2.1, u₅.other r hr.2.2.2.2.2, u₄.other r hr.2.2.2.2.1,
      u₃.other r hr.2.2.2.1, u₂.other r hr.2.1, u₁.other r hr.1]
  · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]

end VG.Proof.Poly1305.X86

end

-- Formerly the module `VerifiedGarbage.Proof.Poly1305.X86.Blocks`.
section

/-!
# Poly1305 on x86 (32-bit): `blocks`
-/

namespace VG.Proof.Poly1305

open Spec.Poly1305

open VG.X86 in
/-- `vg_poly1305_init(state: *mut [u64; 16], key: *const [u8; 32])`. -/
def initX86 : Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 128⟩
    let key : Region := ⟨(arg s 1).setWidth 64, 32⟩
    let args : Region := ⟨argAddr s 0, 8⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [key, args] ∧ s.wr = [state] ∧ state.Disjoint key ∧ args.Disjoint state ∧
      ret.Disjoint state ∧ (arg s 0).toNat + 128 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 32 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 12 ≤ 2 ^ 32
  post s s' := Repr s'.mem ((arg s 0).setWidth 64) (bytesAt s.mem ((arg s 1).setWidth 64) 32) []
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1

open VG.X86 in
/-- `vg_poly1305_blocks(state: *mut [u64; 16], blocks: *const [u8; 16], n:
usize)`. -/
def blocksX86 : Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 128⟩
    let blocks : Region := ⟨(arg s 1).setWidth 64, 16 * (arg s 2).toNat⟩
    let args : Region := ⟨argAddr s 0, 12⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [blocks, args] ∧ s.wr = [state] ∧ state.Disjoint blocks ∧ args.Disjoint state ∧
      ret.Disjoint state ∧ (arg s 0).toNat + 128 ≤ 2 ^ 32 ∧
      (arg s 1).toNat + 16 * (arg s 2).toNat ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 16 ≤ 2 ^ 32
  post s s' := ∀ key msg, Repr s.mem ((arg s 0).setWidth 64) key msg →
    Repr s'.mem ((arg s 0).setWidth 64) key
      (msg ++ bytesAt s.mem ((arg s 1).setWidth 64) (16 * (arg s 2).toNat))
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1 ∧
    arg s₁ 2 = arg s₂ 2

/-- The message's length so far, `count`, from the arguments 1 and 2 (cdecl:
the low word first). -/
def countX86 (s : X86.State) : BitVec 64 := X86.arg s 2 ++ X86.arg s 1

open VG.X86 in
/-- `vg_poly1305_update(state: *mut [u64; 16], count: u64, data: *const u8, len:
usize, scratch: *mut [u64; 16])`: the arguments `state`, the low and high words
of `count`, `data`, `len` and `scratch`. -/
def updateX86 : Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 128⟩
    let data : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
    let scratch : Region := ⟨(arg s 5).setWidth 64, 128⟩
    let args : Region := ⟨argAddr s 0, 24⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [data, args] ∧ s.wr = [state, scratch] ∧ state.Disjoint data ∧ state.Disjoint scratch ∧
      data.Disjoint scratch ∧ args.Disjoint state ∧ args.Disjoint scratch ∧ ret.Disjoint state ∧
      ret.Disjoint scratch ∧ (arg s 0).toNat + 128 ≤ 2 ^ 32 ∧ (arg s 3).toNat + (arg s 4).toNat ≤ 2
          ^ 32 ∧
      (arg s 5).toNat + 128 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 28 ≤ 2 ^ 32
  post s s' := ∀ key msg, Buffered s.mem ((arg s 0).setWidth 64) key msg →
    VG.Proof.Poly1305.countX86 s = BitVec.ofNat 64 msg.length →
    Buffered s'.mem ((arg s 0).setWidth 64) key (msg ++ bytesAt s.mem ((arg s 3).setWidth 64) (arg s
        4).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 6, arg s₁ i = arg s₂ i

open VG.X86 in
/-- `vg_poly1305_finalize(state: *mut [u64; 16], count: u64, out: *mut [u8; 16],
scratch: *mut [u64; 16])`: the arguments `state`, the low and high words of
`count`, `out` and `scratch`. Only the message's length modulo 16 matters (as on
x86-64), so a caller whose message is whole blocks may pass `count = 0`. -/
def finalizeX86 : Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 128⟩
    let out : Region := ⟨(arg s 3).setWidth 64, 16⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, 128⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [args] ∧ s.wr = [state, out, scratch] ∧ state.Disjoint out ∧ state.Disjoint scratch ∧
      out.Disjoint scratch ∧ args.Disjoint state ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
      ret.Disjoint state ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧ (arg s 0).toNat + 128 ≤ 2 ^ 32
          ∧
      (arg s 3).toNat + 16 ≤ 2 ^ 32 ∧ (arg s 4).toNat + 128 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^
          32
  post s s' := ∀ key msg, Buffered s.mem ((arg s 0).setWidth 64) key msg →
    (VG.Proof.Poly1305.countX86 s).toNat % 16 = msg.length % 16 → bytesAt s'.mem ((arg s 3).setWidth 64) 16 = mac key
        msg
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, arg s₁ i = arg s₂ i

end VG.Proof.Poly1305

namespace VG.Proof.Poly1305.X86

open VG VG.X86 VG.Impl.Poly1305.X86
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr)

/-! ## Common to `blocks`, `update` and `finalize` -/

section
variable (s₀ : State)
/-- The state, on entry. -/
abbrev stp : BitVec 32 := arg s₀ 0
/-- The accumulator on entry. -/
abbrev A0 : Nat := leNum (bytesAt s₀.mem ((VG.Proof.Poly1305.X86.stp s₀).setWidth 64) 24)
/-- The clamped `r`. -/
abbrev Rn : Nat :=
  VG.Proof.Poly1305.X86.rval (VG.Proof.Poly1305.X86.r0v s₀.mem (VG.Proof.Poly1305.X86.stp s₀)) (VG.Proof.Poly1305.X86.qv s₀.mem (VG.Proof.Poly1305.X86.stp s₀) 1) (VG.Proof.Poly1305.X86.qv s₀.mem (VG.Proof.Poly1305.X86.stp s₀) 2) (VG.Proof.Poly1305.X86.qv s₀.mem (VG.Proof.Poly1305.X86.stp s₀) 3)
/-- The return address's region. -/
abbrev retR : Region := ⟨(s₀.gpr .esp).setWidth 64, 4⟩
end

theorem arg0_eq (s : State) : s.mem.readW (addr (s.gpr .esp) 4) 32 = arg s 0 := rfl

theorem argAddr_eq (s : State) (i : Nat) : argAddr s i = addr (s.gpr .esp) (4 + 4 * i) := rfl

/-- An argument slot's address, in the argument region. -/
theorem arg_contains {s : State} {n : Nat} (hfit : (s.gpr .esp).toNat + 4 + n ≤ 2 ^ 32) {i : Nat}
    (hi : 4 * i + 4 ≤ n) : (⟨argAddr s 0, n⟩ : Region).Contains (addr (s.gpr .esp) (4 + 4 * i)) 4 :=
  VG.Proof.Poly1305.X86.sub_contains (x := s.gpr .esp) (a := 4) (k := n) (by omega_using [hfit]) (by omega_using []) (by omega_using [hi]) (by decide)

/-- The key (words 6 to 13) is unchanged since entry. -/
theorem key_same {m m' : Mem} {st : BitVec 32} (hfit : st.toNat + 128 ≤ 2 ^ 32)
    (h : ∀ k, 6 ≤ k → k < 14 → VG.Proof.Poly1305.X86.words m' st k = VG.Proof.Poly1305.X86.words m st k) :
    bytesAt m' (st.setWidth 64 + 24) 32 = bytesAt m (st.setWidth 64 + 24) 32 := by
  show bytesAt m' _ (4 * 8) = bytesAt m _ (4 * 8)
  refine VG.Proof.Poly1305.X86.bytesAt_congr_words fun k hk => BitVec.eq_of_toNat_eq ?_
  have := h (6 + k) (by omega_using [hk]) (by omega_using [hk])
  simp only [VG.Proof.Poly1305.X86.words, VG.Proof.Poly1305.X86.wv, VG.Proof.Poly1305.X86.wd] at this
  rw [show (24 : Addr) = BitVec.ofNat 64 24 from rfl, VG.Proof.Poly1305.X86.add_ofNat_add, ← addr_eq (by omega_using [hfit, hk]),
    show 24 + 4 * k = 4 * (6 + k) by omega_using []]
  exact this

/-- The clamped `r` of the key on entry. -/
theorem clamp_key (m : Mem) {st : BitVec 32} (hfit : st.toNat + 128 ≤ 2 ^ 32) :
    clamp (leNum ((bytesAt m (st.setWidth 64 + 24) 32).take 16)) =
      VG.Proof.Poly1305.X86.rval (VG.Proof.Poly1305.X86.r0v m st) (VG.Proof.Poly1305.X86.qv m st 1) (VG.Proof.Poly1305.X86.qv m st 2) (VG.Proof.Poly1305.X86.qv m st 3) := by
  rw [show bytesAt m (st.setWidth 64 + 24) 32 = bytesAt m (st.setWidth 64 + 24) (16 + 16) from rfl,
    Poly1305.bytesAt_add, List.take_left' (Poly1305.length_bytesAt _ _ _),
    VG.Proof.Poly1305.X86.leNum_bytesAt_16, show (24 : Addr) = BitVec.ofNat 64 24 from rfl]
  rw [VG.Proof.Poly1305.X86.w32_off hfit (by decide), VG.Proof.Poly1305.X86.w32_off hfit (by decide), VG.Proof.Poly1305.X86.w32_off hfit (by decide), VG.Proof.Poly1305.X86.w32_off hfit (by decide)]
  have e : ∀ k, VG.Proof.Poly1305.X86.words m st k = VG.Proof.Poly1305.X86.wv m st (4 * k) := fun _ => rfl
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, show 24 + 4 * 2 = 4 * 8 from rfl,
    show 24 + 4 * 3 = 4 * 9 from rfl, show (24 : Nat) = 4 * 6 from rfl, show 24 + 4 = 4 * 7 from rfl]
  rw [VG.Proof.Poly1305.X86.clamp_words4 (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _)]
  have a1 := VG.Proof.Poly1305.X86.mask1_mod (VG.Proof.Poly1305.X86.wv m st (4 * 7))
  have b1 := VG.Proof.Poly1305.X86.mask1_mod (VG.Proof.Poly1305.X86.wv m st (4 * 8))
  have d1 := VG.Proof.Poly1305.X86.mask1_mod (VG.Proof.Poly1305.X86.wv m st (4 * 9))
  simp only [VG.Proof.Poly1305.X86.rval, VG.Proof.Poly1305.X86.r0v, VG.Proof.Poly1305.X86.qv, e, Nat.reduceAdd]
  simp only [VG.Proof.Poly1305.X86.wv] at a1 b1 d1 ⊢
  omega_using [a1, b1, d1]


theorem mod_step {h X M R : Nat} (hv : h % P = X % P) :
    ((h + M) * R) % P = (R * (X + M)) % P % P := by
  rw [Nat.mod_mod, Nat.mul_comm R, Nat.mul_mod, Nat.add_mod, hv, ← Nat.add_mod, ← Nat.mul_mod]

/-- The accumulator on entry is less than `p` if the state represents a message. -/
theorem A0_lt {s₀ : State} {key msg : List Byte} (h : Repr s₀.mem ((VG.Proof.Poly1305.X86.stp s₀).setWidth 64) key msg) :
    VG.Proof.Poly1305.X86.A0 s₀ < P := by
  have := Poly1305.accumulate_lt (clamp (leNum (key.take 16))) msg
  rw [← h.2.2] at this
  exact this

/-! ## `blocks` -/

section
variable (s₀ : State)
abbrev bp : BitVec 32 := arg s₀ 1
abbrev nb : Nat := (arg s₀ 2).toNat
abbrev blR : Region := ⟨(VG.Proof.Poly1305.X86.bp s₀).setWidth 64, 16 * VG.Proof.Poly1305.X86.nb s₀⟩
/-- The first `i` blocks. -/
abbrev blks (i : Nat) : List Byte := bytesAt s₀.mem ((VG.Proof.Poly1305.X86.bp s₀).setWidth 64) (16 * i)
end

structure BPre (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.Poly1305.X86.blR s₀, ⟨argAddr s₀ 0, 12⟩]
  wr : s₀.wr = [VG.Proof.Poly1305.X86.sR (VG.Proof.Poly1305.X86.stp s₀)]
  st_bl : (VG.Proof.Poly1305.X86.sR (VG.Proof.Poly1305.X86.stp s₀)).Disjoint (VG.Proof.Poly1305.X86.blR s₀)
  arg_st : Region.Disjoint ⟨argAddr s₀ 0, 12⟩ (VG.Proof.Poly1305.X86.sR (VG.Proof.Poly1305.X86.stp s₀))
  ret_st : (VG.Proof.Poly1305.X86.retR s₀).Disjoint (VG.Proof.Poly1305.X86.sR (VG.Proof.Poly1305.X86.stp s₀))
  st_fit : (VG.Proof.Poly1305.X86.stp s₀).toNat + 128 ≤ 2 ^ 32
  bl_fit : (VG.Proof.Poly1305.X86.bp s₀).toNat + 16 * VG.Proof.Poly1305.X86.nb s₀ ≤ 2 ^ 32
  sp_fit : (s₀.gpr .esp).toNat + 16 ≤ 2 ^ 32

theorem BPre.of (s₀ : State) (h : Proof.Poly1305.blocksX86.pre s₀) : VG.Proof.Poly1305.X86.BPre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- What holds from `setup` on: the words `F` it left. -/
structure SetupF (s₀ : State) (F : Nat → Nat) : Prop where
  low : ∀ k, k < 18 → k ≠ 5 → F k = VG.Proof.Poly1305.X86.words s₀.mem (VG.Proof.Poly1305.X86.stp s₀) k
  saved : VG.Proof.Poly1305.X86.SavedIn s₀ F
  coefs : VG.Proof.Poly1305.X86.Coefs F (VG.Proof.Poly1305.X86.r0v s₀.mem (VG.Proof.Poly1305.X86.stp s₀)) (VG.Proof.Poly1305.X86.qv s₀.mem (VG.Proof.Poly1305.X86.stp s₀) 1) (VG.Proof.Poly1305.X86.qv s₀.mem (VG.Proof.Poly1305.X86.stp s₀) 2)
    (VG.Proof.Poly1305.X86.qv s₀.mem (VG.Proof.Poly1305.X86.stp s₀) 3)

theorem SetupF.of {s₀ : State} {F : Nat → Nat}
    (hF : ∀ k, (k < 18 ∧ k ≠ 5) ∨ (25 ≤ k ∧ k < 29) → F k = VG.Proof.Poly1305.X86.words s₀.mem (VG.Proof.Poly1305.X86.stp s₀) k)
    (sv : VG.Proof.Poly1305.X86.SavedIn s₀ F) (co : VG.Proof.Poly1305.X86.Coefs F (VG.Proof.Poly1305.X86.r0v s₀.mem (VG.Proof.Poly1305.X86.stp s₀)) (VG.Proof.Poly1305.X86.qv s₀.mem (VG.Proof.Poly1305.X86.stp s₀) 1) (VG.Proof.Poly1305.X86.qv s₀.mem (VG.Proof.Poly1305.X86.stp s₀) 2)
      (VG.Proof.Poly1305.X86.qv s₀.mem (VG.Proof.Poly1305.X86.stp s₀) 3)) : VG.Proof.Poly1305.X86.SetupF s₀ F :=
  ⟨fun k h₁ h₂ => hF k (.inl ⟨h₁, h₂⟩), sv, co⟩

/-- The words that absorbing a block and the final reduction store. -/
theorem not_hS {k : Nat} (h : 5 ≤ k ∧ k < 25 ∨ 29 ≤ k) : k ∉ VG.Proof.Poly1305.X86.hS := by
  simp only [VG.Proof.Poly1305.X86.hS, List.mem_cons, List.not_mem_nil, or_false]; omega_using [h]

/-- The coefficients, in the words `F` of `setup`, unchanged where the words
outside `hS` are. -/
theorem SetupF.coefs' {s₀ : State} {F : Nat → Nat} (hF : VG.Proof.Poly1305.X86.SetupF s₀ F) {g : Nat → Nat}
    (hk : ∀ k < 32, k ∉ VG.Proof.Poly1305.X86.hS → g k = F k) :
    VG.Proof.Poly1305.X86.Coefs g (VG.Proof.Poly1305.X86.r0v s₀.mem (VG.Proof.Poly1305.X86.stp s₀)) (VG.Proof.Poly1305.X86.qv s₀.mem (VG.Proof.Poly1305.X86.stp s₀) 1) (VG.Proof.Poly1305.X86.qv s₀.mem (VG.Proof.Poly1305.X86.stp s₀) 2) (VG.Proof.Poly1305.X86.qv s₀.mem (VG.Proof.Poly1305.X86.stp s₀) 3) :=
  hF.coefs.congr fun k h₁ h₂ => hk k (by omega_using [h₁, h₂]) (VG.Proof.Poly1305.X86.not_hS (.inl ⟨by omega_using [h₁, h₂], h₂⟩))

/-- The state at the start of block `i` (or after the last), with the words
`F` of `setup`. -/
structure BInv (s₀ : State) (F : Nat → Nat) (i : Nat) (s : State) : Prop where
  ctx : VG.Proof.Poly1305.X86.Ctx (VG.Proof.Poly1305.X86.stp s₀) s
  esp : s.gpr .esp = s₀.gpr .esp
  esi : s.gpr .esi = VG.Proof.Poly1305.X86.bp s₀ + BitVec.ofNat 32 (16 * i)
  frame : Frame [VG.Proof.Poly1305.X86.sR (VG.Proof.Poly1305.X86.stp s₀)] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ k < 32, k ∉ VG.Proof.Poly1305.X86.hS → VG.Proof.Poly1305.X86.words s.mem (VG.Proof.Poly1305.X86.stp s₀) k = F k
  acc : VG.Proof.Poly1305.X86.A0 s₀ < P → VG.Proof.Poly1305.X86.words s.mem (VG.Proof.Poly1305.X86.stp s₀) 4 ≤ 4 ∧
    VG.Proof.Poly1305.X86.hw5 (VG.Proof.Poly1305.X86.words s.mem (VG.Proof.Poly1305.X86.stp s₀)) % P = Poly1305.absorbAll (VG.Proof.Poly1305.X86.Rn s₀) (VG.Proof.Poly1305.X86.A0 s₀) (VG.Proof.Poly1305.X86.blks s₀ i) % P

theorem blocks_eq : blocks = .seq (.block (setup ++ ([.mov .esi (.mem (at_ .esp 8)),
    .mov .ecx (.mem (at_ .esp 12)), .alu .test .ecx (.reg .ecx)] : List Instr)))
    (.seq (.ite .e (.block []) (.loop body .ne)) (.block (reduce ++ restore))) := rfl

namespace BPre
variable {s₀ : State} (hp : VG.Proof.Poly1305.X86.BPre s₀)
include hp

theorem argIn {i : Nat} (hi : i < 3) : InRegions (s₀.rd ++ s₀.wr) (addr (s₀.gpr .esp) (4 + 4 * i)) 4 :=
  ⟨⟨argAddr s₀ 0, 12⟩, by rw [hp.rd]; simp only [List.cons_append, List.nil_append, List.mem_cons, Region.mk.injEq, true_or, or_true], VG.Proof.Poly1305.X86.arg_contains (n := 12) (by have := hp.sp_fit; omega_using [this])
    (by omega_using [hi])⟩

/-- An argument, in memory the code has written only in the state. -/
theorem arg_same {m : Mem} (hf : Frame [VG.Proof.Poly1305.X86.sR (VG.Proof.Poly1305.X86.stp s₀)] s₀.mem m) {i : Nat} (hi : i < 3) :
    m.readW (addr (s₀.gpr .esp) (4 + 4 * i)) 32 = arg s₀ i :=
  hf.readW (VG.Proof.Poly1305.X86.arg_contains (n := 12) (by have := hp.sp_fit; omega_using [this]) (by omega_using [hi])) (by simpa using hp.arg_st)
    (by decide)

end BPre

/-- The accumulator on entry, in the words `F` of `setup`. -/
theorem acc_entry {s₀ : State} (hfit : (VG.Proof.Poly1305.X86.stp s₀).toNat + 128 ≤ 2 ^ 32) {F : Nat → Nat} (hF : VG.Proof.Poly1305.X86.SetupF s₀ F)
    {m : Mem} (hk : ∀ k < 5, VG.Proof.Poly1305.X86.words m (VG.Proof.Poly1305.X86.stp s₀) k = F k) (hA : VG.Proof.Poly1305.X86.A0 s₀ < P) :
    VG.Proof.Poly1305.X86.words m (VG.Proof.Poly1305.X86.stp s₀) 4 ≤ 4 ∧ VG.Proof.Poly1305.X86.hw5 (VG.Proof.Poly1305.X86.words m (VG.Proof.Poly1305.X86.stp s₀)) % P = Poly1305.absorbAll (VG.Proof.Poly1305.X86.Rn s₀) (VG.Proof.Poly1305.X86.A0 s₀) [] % P := by
  have hlow : ∀ k, k < 5 → VG.Proof.Poly1305.X86.words m (VG.Proof.Poly1305.X86.stp s₀) k = VG.Proof.Poly1305.X86.words s₀.mem (VG.Proof.Poly1305.X86.stp s₀) k := fun k hk' => by
    rw [hk k hk', hF.low k (by omega_using [hk']) (by omega_using [hk'])]
  obtain ⟨-, h4, hv⟩ := VG.Proof.Poly1305.X86.acc_words hfit (VG.Proof.Poly1305.X86.words_ok s₀.mem _) hA
  refine ⟨by rw [hlow 4 (by decide)]; omega_using [h4], ?_⟩
  rw [Poly1305.absorbAll_nil]
  simp only [VG.Proof.Poly1305.X86.hw5, hlow 0 (by decide), hlow 1 (by decide), hlow 2 (by decide), hlow 3 (by decide),
    hlow 4 (by decide)]
  rw [show VG.Proof.Poly1305.X86.A0 s₀ = VG.Proof.Poly1305.X86.hw5 (VG.Proof.Poly1305.X86.words s₀.mem (VG.Proof.Poly1305.X86.stp s₀)) from hv]

theorem prologue_ok {s₀ : State} (hp : VG.Proof.Poly1305.X86.BPre s₀) :
    WP isa (.block (setup ++ ([.mov .esi (.mem (at_ .esp 8)), .mov .ecx (.mem (at_ .esp 12)),
      .alu .test .ecx (.reg .ecx)] : List Instr))) s₀ fun s => ∃ F, VG.Proof.Poly1305.X86.SetupF s₀ F ∧
        VG.Proof.Poly1305.X86.BInv s₀ F 0 s ∧ s.zf = some (arg s₀ 2 &&& arg s₀ 2 == 0) := by
  have hfit := hp.st_fit
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86.setup_ok (VG.Proof.Poly1305.X86.arg0_eq s₀) (hp.argIn (i := 0) (by decide)) hfit
    (by rw [hp.wr]; exact List.mem_singleton_self _)) fun s₁ ⟨F, A₁, c₁, hF, sv, co⟩ => ?_)
  have esp₁ := A₁.gpr .esp (by decide)
  have hF' := SetupF.of hF sv co
  refine VG.Proof.Poly1305.X86.wp_movm (a := addr (s₀.gpr .esp) (4 + 4 * 1)) (by rw [VG.Proof.Poly1305.X86.ea_at, esp₁])
    (by rw [A₁.rd, A₁.wr]; exact hp.argIn (by decide)) fun s₂ u₂ _ => ?_
  refine VG.Proof.Poly1305.X86.wp_movm (a := addr (s₀.gpr .esp) (4 + 4 * 2)) (by rw [VG.Proof.Poly1305.X86.ea_at, u₂.other _ (by decide), esp₁])
    (by rw [u₂.rd, u₂.wr, A₁.rd, A₁.wr]; exact hp.argIn (by decide)) fun s₃ u₃ _ => ?_
  refine VG.Proof.Poly1305.X86.wp_test fun s₄ k₄ z₄ => WP.block_nil ⟨F, hF', ?_, ?_⟩
  · have hm : s₄.mem = s₁.mem := by rw [k₄.2.1, u₃.mem, u₂.mem]
    refine ⟨c₁.keep (by rw [k₄.1 _ (by simp only [List.not_mem_nil, not_false_eq_true]), u₃.other _ (by decide), u₂.other _ (by decide)])
      (by rw [k₄.2.2.2, u₃.wr, u₂.wr]), ?_, ?_, ?_, ?_, ?_, fun k hk _ => ?_, fun hA => ?_⟩
    · rw [k₄.1 _ (by simp only [List.not_mem_nil, not_false_eq_true]), u₃.other _ (by decide), u₂.other _ (by decide), esp₁]
    · rw [k₄.1 _ (by simp only [List.not_mem_nil, not_false_eq_true]), u₃.other _ (by decide), u₂.gpr, hp.arg_same A₁.frame (i := 1) (by decide)]
      simp only [Nat.mul_zero, BitVec.add_zero]
    · rw [hm]; exact A₁.frame
    · rw [k₄.2.2.1, u₃.rd, u₂.rd, A₁.rd]
    · rw [k₄.2.2.2, u₃.wr, u₂.wr, A₁.wr]
    · rw [hm, VG.Proof.Poly1305.X86.words_eq A₁.words hk]
    · exact VG.Proof.Poly1305.X86.acc_entry hfit hF' (fun k hk => by rw [hm, VG.Proof.Poly1305.X86.words_eq A₁.words (by omega_using [hk])]) hA
  · rw [z₄, u₃.gpr, u₂.mem, hp.arg_same A₁.frame (i := 2) (by decide)]

theorem blk_addr {bp : BitVec 32} {n i d : Nat} (hfit : bp.toNat + 16 * n ≤ 2 ^ 32) (hi : i < n)
    (hd : d + 4 ≤ 16) :
    addr (bp + BitVec.ofNat 32 (16 * i)) d = bp.setWidth 64 + BitVec.ofNat 64 (16 * i + d) := by
  simp only [addr]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := bp.isLt
  rw [Nat.mod_eq_of_lt (a := 16 * i) (by omega_using [hfit, hi]), Nat.mod_eq_of_lt (a := bp.toNat + 16 * i) (by omega_using [hfit, hi]),
    Nat.mod_eq_of_lt (a := d) (by omega_using [hd]), Nat.mod_eq_of_lt (a := bp.toNat + 16 * i + d) (by omega_using [hfit, hi, hd]),
    Nat.mod_eq_of_lt (a := bp.toNat + 16 * i + d) (by omega_using [hfit, hi, hd]), Nat.mod_eq_of_lt (a := bp.toNat) (by omega_using []),
    Nat.mod_eq_of_lt (a := 16 * i + d) (by omega_using [hfit, hi, hd]), Nat.mod_eq_of_lt (a := bp.toNat + (16 * i + d)) (by omega_using [hfit, hi, hd])]
  omega_using []

theorem blk_contains {bp : BitVec 32} {n i d : Nat} (hfit : bp.toNat + 16 * n ≤ 2 ^ 32) (hi : i < n)
    (hd : d + 4 ≤ 16) {k : Nat} (_hk : 0 < k) (hk' : d + k ≤ 16) :
    (⟨bp.setWidth 64, 16 * n⟩ : Region).Contains (addr (bp + BitVec.ofNat 32 (16 * i)) d) k := by
  rw [VG.Proof.Poly1305.X86.blk_addr hfit hi hd]
  exact Offset.contains_base _ (by omega_using [hi, hk']) (by omega_using [hfit, hi, hd])

theorem blk_sub {bp : BitVec 32} {n i d : Nat} (hfit : bp.toNat + 16 * n ≤ 2 ^ 32) (hi : i < n)
    (hd : d + 4 ≤ 16) : Region.Sub (VG.Proof.Poly1305.X86.sub (bp + BitVec.ofNat 32 (16 * i)) d 4) ⟨bp.setWidth 64, 16 * n⟩ := by
  rw [VG.Proof.Poly1305.X86.sub, VG.Proof.Poly1305.X86.blk_addr hfit hi hd]
  exact Offset.sub_base _ (by omega_using [hi, hd])

namespace BPre
variable {s₀ : State} (hp : VG.Proof.Poly1305.X86.BPre s₀)
include hp

theorem blkIn {s : State} {i : Nat} (hi : i < VG.Proof.Poly1305.X86.nb s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hesi : s.gpr .esi = VG.Proof.Poly1305.X86.bp s₀ + BitVec.ofNat 32 (16 * i)) : VG.Proof.Poly1305.X86.BlkIn s := fun d hd => by
  rw [hrd, hwr, hesi, hp.rd]
  exact ⟨VG.Proof.Poly1305.X86.blR s₀, by simp only [List.cons_append, List.nil_append, List.mem_cons, Region.mk.injEq, true_or], VG.Proof.Poly1305.X86.blk_contains hp.bl_fit hi hd (by decide) (by omega_using [hd])⟩

theorem blk_disj {i : Nat} (hi : i < VG.Proof.Poly1305.X86.nb s₀) {k : Nat} (_hk : k < 4) :
    (VG.Proof.Poly1305.X86.sub (VG.Proof.Poly1305.X86.bp s₀ + BitVec.ofNat 32 (16 * i)) (4 * k) 4).Disjoint (VG.Proof.Poly1305.X86.sR (VG.Proof.Poly1305.X86.stp s₀)) :=
  (hp.st_bl.sub_right (VG.Proof.Poly1305.X86.blk_sub hp.bl_fit hi (by omega_using [_hk]))).symm

/-- The value of block `i`, with the `0x01` byte appended: its four words and `2¹²⁸`. -/
theorem block_value {m : Mem} (hf : Frame [VG.Proof.Poly1305.X86.sR (VG.Proof.Poly1305.X86.stp s₀)] s₀.mem m) {i : Nat} (hi : i < VG.Proof.Poly1305.X86.nb s₀) :
    VG.Proof.Poly1305.X86.blkv m (VG.Proof.Poly1305.X86.bp s₀ + BitVec.ofNat 32 (16 * i)) 1 =
      leNum (bytesAt s₀.mem ((VG.Proof.Poly1305.X86.bp s₀).setWidth 64 + BitVec.ofNat 64 (16 * i)) 16 ++ [0x01]) := by
  have hw : ∀ k < 4, VG.Proof.Poly1305.X86.wv m (VG.Proof.Poly1305.X86.bp s₀ + BitVec.ofNat 32 (16 * i)) (4 * k) =
      VG.Proof.Poly1305.X86.w32 s₀.mem ((VG.Proof.Poly1305.X86.bp s₀).setWidth 64 + BitVec.ofNat 64 (16 * i)) k := fun k hk => by
    show (VG.Proof.Poly1305.X86.wd m _ (4 * k)).toNat = _
    rw [VG.Proof.Poly1305.X86.wd_frame hf (by simpa using hp.blk_disj hi hk)]
    simp only [VG.Proof.Poly1305.X86.wd, VG.Proof.Poly1305.X86.w32]
    rw [VG.Proof.Poly1305.X86.blk_addr hp.bl_fit hi (by omega_using [hk]), VG.Proof.Poly1305.X86.add_ofNat_add]
  rw [Poly1305.leNum_append, Poly1305.length_bytesAt, VG.Proof.Poly1305.X86.leNum_bytesAt_16, ← hw 0 (by decide),
    ← hw 1 (by decide), ← hw 2 (by decide), ← hw 3 (by decide)]
  simp only [VG.Proof.Poly1305.X86.blkv, Spec.Poly1305.leNum]
  rfl

end BPre

theorem blks_succ (s₀ : State) (i : Nat) :
    VG.Proof.Poly1305.X86.blks s₀ (i + 1) = VG.Proof.Poly1305.X86.blks s₀ i ++ bytesAt s₀.mem ((VG.Proof.Poly1305.X86.bp s₀).setWidth 64 + BitVec.ofNat 64 (16 * i)) 16 := by
  simp only [VG.Proof.Poly1305.X86.blks]
  rw [show 16 * (i + 1) = 16 * i + 16 by omega_using [], Poly1305.bytesAt_add]


theorem eval_ne' (s : State) : eval .ne s = s.zf.map (!·) := rfl

theorem body_eq : body = .block (absorb 1 ++ (.alu .add .esi (.imm 16) :: atEnd)) := by
  simp only [body, List.append_assoc, List.singleton_append]

theorem atEnd_eq : atEnd = [.mov .eax (.mem (at_ .esp 12)), .alu .add .eax (.reg .eax),
    .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax),
    .mov .ecx (.mem (at_ .esp 8)), .alu .add .eax (.reg .ecx), .alu .cmp .eax (.reg .esi)] := rfl

theorem add16_eq (n : BitVec 32) : n + n + (n + n) + (n + n + (n + n)) + (n + n + (n + n) + (n + n + (n + n))) =
    BitVec.ofNat 32 (16 * n.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega_using []

/-- `16 n + b`, from the arguments `n` at `[esp + 12]` and `b` at `[esp + 8]`,
compared with `esi`. -/
theorem atEnd_ok {s : State} {n b : BitVec 32} (hn : s.mem.readW (addr (s.gpr .esp) 12) 32 = n)
    (hb : s.mem.readW (addr (s.gpr .esp) 8) 32 = b)
    (h12 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 12) 4)
    (h8 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 8) 4) :
    WP isa (.block atEnd) s fun s' => VG.Proof.Poly1305.X86.Keeps [.eax, .ecx] s s' ∧
      s'.zf = some (BitVec.ofNat 32 (16 * n.toNat) + b - s.gpr .esi == 0) := by
  rw [VG.Proof.Poly1305.X86.atEnd_eq]
  refine VG.Proof.Poly1305.X86.wp_movm (a := addr (s.gpr .esp) 12) (VG.Proof.Poly1305.X86.ea_at _ _ _) h12 fun s₁ u₁ _ => ?_
  refine VG.Proof.Poly1305.X86.wp_addx (VG.Proof.Poly1305.X86.readSrc_reg _ _) fun s₂ u₂ _ => VG.Proof.Poly1305.X86.wp_addx (VG.Proof.Poly1305.X86.readSrc_reg _ _) fun s₃ u₃ _ => ?_
  refine VG.Proof.Poly1305.X86.wp_addx (VG.Proof.Poly1305.X86.readSrc_reg _ _) fun s₄ u₄ _ => VG.Proof.Poly1305.X86.wp_addx (VG.Proof.Poly1305.X86.readSrc_reg _ _) fun s₅ u₅ _ => ?_
  have k₅ : VG.Proof.Poly1305.X86.Keeps [.eax] s s₅ := ⟨fun r hr => by
      have hr' : r ≠ .eax := by simpa using hr
      rw [u₅.other r hr', u₄.other r hr', u₃.other r hr', u₂.other r hr', u₁.other r hr'],
    by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem], by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd],
    by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]⟩
  refine VG.Proof.Poly1305.X86.wp_movm (a := addr (s.gpr .esp) 8) (by rw [VG.Proof.Poly1305.X86.ea_at, k₅.gpr']) (by
    rw [k₅.2.2.1, k₅.2.2.2]; exact h8) fun s₆ u₆ _ => ?_
  refine VG.Proof.Poly1305.X86.wp_addx (VG.Proof.Poly1305.X86.readSrc_reg _ _) fun s₇ u₇ _ => ?_
  refine VG.Proof.Poly1305.X86.wp_cmpx (VG.Proof.Poly1305.X86.readSrc_reg _ _) fun s₈ k₈ z₈ _ => WP.block_nil ⟨?_, ?_⟩
  · refine ⟨fun r hr => ?_, by rw [k₈.2.1, u₇.mem, u₆.mem, k₅.2.1], by rw [k₈.2.2.1, u₇.rd, u₆.rd, k₅.2.2.1],
      by rw [k₈.2.2.2, u₇.wr, u₆.wr, k₅.2.2.2]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [k₈.1 r (by simp only [List.not_mem_nil, not_false_eq_true]), u₇.other r hr.1, u₆.other r hr.2, k₅.1 r (by simpa using hr.1)]
  · have e₇ : s₇.gpr .eax = BitVec.ofNat 32 (16 * n.toNat) + b := by
      rw [u₇.gpr, u₆.other _ (by decide), u₆.gpr, k₅.2.1, hb, u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr, hn,
        VG.Proof.Poly1305.X86.add16_eq]
    have e₇' : s₇.gpr .esi = s.gpr .esi := by
      rw [u₇.other _ (by decide), u₆.other _ (by decide), k₅.gpr' (r := .esi)]
    rw [z₈, e₇, e₇']

theorem end_eq {bp : BitVec 32} {n i : Nat} (hi : i < n) :
    BitVec.ofNat 32 (16 * n) + bp - (bp + BitVec.ofNat 32 (16 * i) + 16) =
      BitVec.ofNat 32 (16 * (n - (i + 1))) := by
  apply BitVec.eq_of_toNat_eq
  have := bp.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [show (16 : BitVec 32).toNat = 16 from rfl]
  omega_using [hi]

theorem ofNat32_beq_zero {k : Nat} (h : k < 2 ^ 32) : (BitVec.ofNat 32 k == 0) = decide (k = 0) := by
  by_cases hk : k = 0
  · simp only [hk, BitVec.ofNat_eq_ofNat, BEq.rfl, decide_true]
  · simp only [hk, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this
    exact hk this

theorem body_ok {s₀ : State} (hp : VG.Proof.Poly1305.X86.BPre s₀) {F : Nat → Nat} (hF : VG.Proof.Poly1305.X86.SetupF s₀ F) {i : Nat}
    (hi : i < VG.Proof.Poly1305.X86.nb s₀) {s : State} (hL : VG.Proof.Poly1305.X86.BInv s₀ F i s) :
    WP isa body s fun s' =>
      (eval .ne s' = some false ∧ VG.Proof.Poly1305.X86.BInv s₀ F (VG.Proof.Poly1305.X86.nb s₀) s') ∨
      (eval .ne s' = some true ∧ i + 1 < VG.Proof.Poly1305.X86.nb s₀ ∧ VG.Proof.Poly1305.X86.BInv s₀ F (i + 1) s') := by
  have hfit := hp.st_fit
  rw [VG.Proof.Poly1305.X86.body_eq]
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86.absorbFull_ok hL.ctx (hp.blkIn hi hL.rd hL.wr hL.esi)
    (fun k hk => by rw [hL.esi]; exact hp.blk_disj hi hk) 1 (by decide) (C := VG.Proof.Poly1305.X86.A0 s₀ < P)
    (fun hA => ⟨hF.coefs' fun k hk hS => hL.keep k hk hS, (hL.acc hA).1⟩)) fun s₁ ⟨S₁, h₁⟩ => ?_)
  have c₁ := hL.ctx.keep (S₁.gpr _ (by decide)) S₁.wr
  refine VG.Proof.Poly1305.X86.wp_addx (VG.Proof.Poly1305.X86.readSrc_imm _ _) fun s₂ u₂ _ => ?_
  have esp₂ : s₂.gpr .esp = s₀.gpr .esp := by rw [u₂.other _ (by decide), S₁.gpr _ (by decide), hL.esp]
  have hfr₂ : Frame [VG.Proof.Poly1305.X86.sR (VG.Proof.Poly1305.X86.stp s₀)] s₀.mem s₂.mem := by rw [u₂.mem]; exact hL.frame.trans S₁.frame
  have hrd₂ : s₂.rd = s₀.rd := by rw [u₂.rd, S₁.rd, hL.rd]
  have hwr₂ : s₂.wr = s₀.wr := by rw [u₂.wr, S₁.wr, hL.wr]
  have hesi₂ : s₂.gpr .esi = VG.Proof.Poly1305.X86.bp s₀ + BitVec.ofNat 32 (16 * i) + 16 := by
    rw [u₂.gpr, S₁.gpr _ (by decide), hL.esi]
  refine WP.mono (VG.Proof.Poly1305.X86.atEnd_ok (n := arg s₀ 2) (b := arg s₀ 1)
    (by rw [esp₂]; exact hp.arg_same hfr₂ (i := 2) (by decide))
    (by rw [esp₂]; exact hp.arg_same hfr₂ (i := 1) (by decide))
    (by rw [hrd₂, hwr₂, esp₂]; exact hp.argIn (i := 2) (by decide))
    (by rw [hrd₂, hwr₂, esp₂]; exact hp.argIn (i := 1) (by decide))) fun s₃ ⟨k₃, z₃⟩ => ?_
  have hm₃ : s₃.mem = s₁.mem := by rw [k₃.2.1, u₂.mem]
  have hc : VG.Proof.Poly1305.X86.BInv s₀ F (i + 1) s₃ := by
    refine ⟨c₁.keep (by rw [k₃.gpr', u₂.other _ (by decide)]) (by rw [k₃.2.2.2, u₂.wr]),
      by rw [k₃.gpr']; exact esp₂, ?_, by rw [k₃.2.1]; exact hfr₂, by rw [k₃.2.2.1]; exact hrd₂,
      by rw [k₃.2.2.2]; exact hwr₂, fun k hk hS => ?_, fun hA => ?_⟩
    · rw [k₃.gpr', hesi₂, BitVec.add_assoc, show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl,
        ← BitVec.ofNat_add, show 16 * i + 16 = 16 * (i + 1) by omega_using []]
    · rw [hm₃, show VG.Proof.Poly1305.X86.words s₁.mem (VG.Proof.Poly1305.X86.stp s₀) k = VG.Proof.Poly1305.X86.wv s₁.mem (VG.Proof.Poly1305.X86.stp s₀) (4 * k) from rfl, S₁.same k hk hS]
      exact hL.keep k hk hS
    · obtain ⟨h4, hv⟩ := h₁ hA
      obtain ⟨-, hv₀⟩ := hL.acc hA
      refine ⟨by rw [hm₃]; exact h4, ?_⟩
      have h16 : (VG.Proof.Poly1305.X86.blks s₀ i).length % 16 = 0 := by simp only [VG.Proof.Poly1305.X86.blks, Poly1305.length_bytesAt]; omega_using []
      have hb1 : 0 < (bytesAt s₀.mem ((VG.Proof.Poly1305.X86.bp s₀).setWidth 64 + BitVec.ofNat 64 (16 * i)) 16).length := by
        rw [Poly1305.length_bytesAt]; omega_using []
      have hb2 : (bytesAt s₀.mem ((VG.Proof.Poly1305.X86.bp s₀).setWidth 64 + BitVec.ofNat 64 (16 * i)) 16).length ≤ 16 := by
        rw [Poly1305.length_bytesAt]
      rw [hm₃, hv, hL.esi, show (1 : BitVec 32).toNat = 1 from rfl, hp.block_value hL.frame hi,
        VG.Proof.Poly1305.X86.mod_step hv₀, VG.Proof.Poly1305.X86.blks_succ, Poly1305.absorbAll_append h16, Poly1305.absorbAll_block hb1 hb2]
  have hev : eval .ne s₃ = some (!(decide (16 * (VG.Proof.Poly1305.X86.nb s₀ - (i + 1)) = 0))) := by
    rw [VG.Proof.Poly1305.X86.eval_ne', z₃, hesi₂, VG.Proof.Poly1305.X86.end_eq hi, VG.Proof.Poly1305.X86.ofNat32_beq_zero (by have := hp.bl_fit; omega_using [hi, this])]
    rfl
  by_cases hlast : i + 1 = VG.Proof.Poly1305.X86.nb s₀
  · left
    exact ⟨by rw [hev, ← hlast]; simp only [Nat.sub_self, Nat.mul_zero, decide_true, Bool.not_true], hlast ▸ hc⟩
  · right
    exact ⟨by rw [hev]; simp only [Option.some.injEq, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]; omega_using [hi, hlast], by omega_using [hi, hlast], hc⟩

/-! ## Epilogue -/

/-- `h` of a state that represents a message, and its key. -/
theorem repr_acc {s₀ : State} {key msg : List Byte} (hfit : (VG.Proof.Poly1305.X86.stp s₀).toNat + 128 ≤ 2 ^ 32)
    (h : Repr s₀.mem ((VG.Proof.Poly1305.X86.stp s₀).setWidth 64) key msg) :
    clamp (leNum (key.take 16)) = VG.Proof.Poly1305.X86.Rn s₀ ∧ accumulate (VG.Proof.Poly1305.X86.Rn s₀) msg = VG.Proof.Poly1305.X86.A0 s₀ := by
  have hk : bytesAt s₀.mem ((VG.Proof.Poly1305.X86.stp s₀).setWidth 64 + 24) 32 = key := h.2.1
  have hc : clamp (leNum (key.take 16)) = VG.Proof.Poly1305.X86.Rn s₀ := by rw [← hk, VG.Proof.Poly1305.X86.clamp_key _ hfit]
  exact ⟨hc, by rw [← hc, VG.Proof.Poly1305.X86.A0, h.2.2]⟩

/-- What each function leaves in the registers: those `setup` saved. -/
theorem abi_of {s₀ s : State} {F : Nat → Nat} (hsv : VG.Proof.Poly1305.X86.SavedIn s₀ F)
    (hb : VG.Proof.Poly1305.X86.v s .ebx = F 29) (hs : VG.Proof.Poly1305.X86.v s .esi = F 30) (hd : VG.Proof.Poly1305.X86.v s .edi = F 31) (hp : VG.Proof.Poly1305.X86.v s .ebp = F 5)
    (hsp : s.gpr .esp = s₀.gpr .esp) (hret : s.mem.readW ((s₀.gpr .esp).setWidth 64) 32 =
      s₀.mem.readW ((s₀.gpr .esp).setWidth 64) 32) : abiPreserved s₀ s := by
  obtain ⟨b, si, di, bp⟩ := hsv
  refine ⟨fun r hr => ?_, hret⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact BitVec.eq_of_toNat_eq (hb.trans b)
  · exact BitVec.eq_of_toNat_eq (hs.trans si)
  · exact BitVec.eq_of_toNat_eq (hd.trans di)
  · exact BitVec.eq_of_toNat_eq (hp.trans bp)
  · exact hsp

/-- The final reduction and the restoring of the registers: they leave the
reduced `h` and a zero word 5, and the words `hS` do not include is unchanged. -/
theorem finish_ok {st : BitVec 32} {s : State} (hc : VG.Proof.Poly1305.X86.Ctx st s) :
    WP isa (.block (reduce ++ restore)) s fun s' =>
      VG.Proof.Poly1305.X86.v s' .ebx = VG.Proof.Poly1305.X86.words s.mem st 29 ∧ VG.Proof.Poly1305.X86.v s' .esi = VG.Proof.Poly1305.X86.words s.mem st 30 ∧ VG.Proof.Poly1305.X86.v s' .edi = VG.Proof.Poly1305.X86.words s.mem st 31 ∧
      VG.Proof.Poly1305.X86.v s' .ebp = VG.Proof.Poly1305.X86.words s.mem st 5 ∧ s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [VG.Proof.Poly1305.X86.sR st] s.mem s'.mem ∧ VG.Proof.Poly1305.X86.words s'.mem st 5 = 0 ∧
      (∀ k < 32, k ∉ VG.Proof.Poly1305.X86.hS → k ≠ 5 → VG.Proof.Poly1305.X86.words s'.mem st k = VG.Proof.Poly1305.X86.words s.mem st k) ∧
      (VG.Proof.Poly1305.X86.words s.mem st 4 ≤ 4 → ∀ k < 5, VG.Proof.Poly1305.X86.words s'.mem st k = VG.Proof.Poly1305.X86.words s.mem st k ∨ True) ∧
      (VG.Proof.Poly1305.X86.words s.mem st 4 ≤ 4 → VG.Proof.Poly1305.X86.hw5 (VG.Proof.Poly1305.X86.words s'.mem st) = VG.Proof.Poly1305.X86.hw5 (VG.Proof.Poly1305.X86.words s.mem st) % P) := by
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86.reduceFull_ok hc) fun s₁ ⟨S₁, h₁⟩ => ?_)
  have c₁ := hc.keep (S₁.gpr _ (by decide)) S₁.wr
  refine WP.mono (VG.Proof.Poly1305.X86.restore_ok c₁) fun s₂ ⟨b₂, si₂, di₂, bp₂, sp₂, A₂⟩ => ?_
  have hw : ∀ k < 32, VG.Proof.Poly1305.X86.words s₂.mem st k = VG.Proof.Poly1305.X86.upd (VG.Proof.Poly1305.X86.words s₁.mem st) 5 0 k := fun k hk => A₂.words k hk
  have h1 : ∀ k < 32, k ∉ VG.Proof.Poly1305.X86.hS → VG.Proof.Poly1305.X86.words s₁.mem st k = VG.Proof.Poly1305.X86.words s.mem st k := fun k hk hS =>
    S₁.same k hk hS
  refine ⟨?_, ?_, ?_, ?_, by rw [sp₂, S₁.gpr _ (by decide)], by rw [A₂.rd, S₁.rd], by rw [A₂.wr, S₁.wr],
    S₁.frame.trans A₂.frame, by rw [hw 5 (by decide), VG.Proof.Poly1305.X86.upd_same], fun k hk hS h5 => ?_, fun _ _ _ => .inr trivial,
    fun h4 => ?_⟩
  · rw [b₂, h1 29 (by decide) (by decide)]
  · rw [si₂, h1 30 (by decide) (by decide)]
  · rw [di₂, h1 31 (by decide) (by decide)]
  · rw [bp₂, h1 5 (by decide) (by decide)]
  · rw [hw k hk, VG.Proof.Poly1305.X86.upd_ne _ _ h5, h1 k hk hS]
  · obtain ⟨hr, -⟩ := h₁ h4
    simp only [VG.Proof.Poly1305.X86.hw5, hw 0 (by decide), hw 1 (by decide), hw 2 (by decide), hw 3 (by decide), hw 4 (by decide),
      VG.Proof.Poly1305.X86.upd_ne _ _ (show (0 : Nat) ≠ 5 by decide), VG.Proof.Poly1305.X86.upd_ne _ _ (show (1 : Nat) ≠ 5 by decide),
      VG.Proof.Poly1305.X86.upd_ne _ _ (show (2 : Nat) ≠ 5 by decide), VG.Proof.Poly1305.X86.upd_ne _ _ (show (3 : Nat) ≠ 5 by decide),
      VG.Proof.Poly1305.X86.upd_ne _ _ (show (4 : Nat) ≠ 5 by decide)]
    exact hr

theorem blocks_epilogue_ok {s₀ : State} (hp : VG.Proof.Poly1305.X86.BPre s₀) {F : Nat → Nat} (hF : VG.Proof.Poly1305.X86.SetupF s₀ F) {s : State}
    (hL : VG.Proof.Poly1305.X86.BInv s₀ F (VG.Proof.Poly1305.X86.nb s₀) s) :
    WP isa (.block (reduce ++ restore)) s
      fun s' => abiPreserved s₀ s' ∧ Proof.Poly1305.blocksX86.post s₀ s' := by
  have hfit := hp.st_fit
  refine WP.mono (VG.Proof.Poly1305.X86.finish_ok hL.ctx) fun s₂ ⟨b₂, si₂, di₂, bp₂, sp₂, _, _, fr₂, z₂, hk₂, _, hr₂⟩ => ?_
  have hframe : Frame [VG.Proof.Poly1305.X86.sR (VG.Proof.Poly1305.X86.stp s₀)] s₀.mem s₂.mem := hL.frame.trans fr₂
  refine ⟨VG.Proof.Poly1305.X86.abi_of hF.saved ?_ ?_ ?_ ?_ (by rw [sp₂, hL.esp]) ?_, fun key msg hrep => ?_⟩
  · rw [b₂, hL.keep 29 (by decide) (by decide)]
  · rw [si₂, hL.keep 30 (by decide) (by decide)]
  · rw [di₂, hL.keep 31 (by decide) (by decide)]
  · rw [bp₂, hL.keep 5 (by decide) (by decide)]
  · exact hframe.readW (Region.contains_self _ _) (by simpa using hp.ret_st) (by decide)
  · have hA := VG.Proof.Poly1305.X86.A0_lt hrep
    obtain ⟨hcl, hac⟩ := VG.Proof.Poly1305.X86.repr_acc hfit hrep
    obtain ⟨h4, hv⟩ := hL.acc hA
    refine ⟨?_, ?_, ?_⟩
    · rw [List.length_append, Poly1305.length_bytesAt]; have := hrep.1; omega_using [this]
    · rw [VG.Proof.Poly1305.X86.key_same hfit fun k h₁ h₂ => ?_]
      · exact hrep.2.1
      · rw [hk₂ k (by omega_using [h₁, h₂]) (VG.Proof.Poly1305.X86.not_hS (.inl ⟨by omega_using [h₁, h₂], by omega_using [h₁, h₂]⟩)) (by omega_using [h₁, h₂]),
          hL.keep k (by omega_using [h₁, h₂]) (VG.Proof.Poly1305.X86.not_hS (.inl ⟨by omega_using [h₁, h₂], by omega_using [h₁, h₂]⟩)), hF.low k (by omega_using [h₁, h₂]) (by omega_using [h₁, h₂])]
    · rw [VG.Proof.Poly1305.X86.leNum_acc hfit (VG.Proof.Poly1305.X86.words_ok _ _), z₂, hcl, Poly1305.accumulate_append hrep.1, hac, hr₂ h4, hv,
        Nat.mod_eq_of_lt (Poly1305.absorbAll_lt hA _)]
      simp only [Nat.reducePow, Nat.mul_zero, Nat.add_zero]

/-! ## The whole function -/

theorem blocks_correct {s₀ : State} (hp : VG.Proof.Poly1305.X86.BPre s₀) :
    WP isa blocks s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Poly1305.blocksX86.post s₀ s' := by
  rw [VG.Proof.Poly1305.X86.blocks_eq]
  refine WP.seq (WP.mono (VG.Proof.Poly1305.X86.prologue_ok hp) fun s₁ ⟨F, hF, hL₀, hz⟩ => ?_)
  refine WP.seq (WP.mono (Q := VG.Proof.Poly1305.X86.BInv s₀ F (VG.Proof.Poly1305.X86.nb s₀)) ?_ fun s₂ hc₂ => VG.Proof.Poly1305.X86.blocks_epilogue_ok hp hF hc₂)
  refine WP.ite (arg s₀ 2 &&& arg s₀ 2 == 0) (by simp only [eval, hz, BitVec.and_self, BitVec.ofNat_eq_ofNat]) (fun h => ?_) (fun h => ?_)
  · have h0 : VG.Proof.Poly1305.X86.nb s₀ = 0 := by simp only [BitVec.and_self, BitVec.ofNat_eq_ofNat, beq_iff_eq] at h; simp only [VG.Proof.Poly1305.X86.nb, h, BitVec.toNat_ofNat, Nat.reducePow, Nat.zero_mod]
    exact WP.block_nil (M := isa) (h0 ▸ hL₀)
  · have hpos : 0 < VG.Proof.Poly1305.X86.nb s₀ := by
      simp only [BitVec.and_self, beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = VG.Proof.Poly1305.X86.nb s₀ - i ∧ i < VG.Proof.Poly1305.X86.nb s₀ ∧ VG.Proof.Poly1305.X86.BInv s₀ F i s
    have hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
        (eval .ne s' = some false ∧ VG.Proof.Poly1305.X86.BInv s₀ F (VG.Proof.Poly1305.X86.nb s₀) s') ∨
        (eval .ne s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (VG.Proof.Poly1305.X86.body_ok hp hF hi hL) fun s' h => ?_
      rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, VG.Proof.Poly1305.X86.nb s₀ - (i + 1), by omega_using [hi'], i + 1, rfl, hi', hL'⟩
    exact WP.loop (M := isa) Inv hstep (VG.Proof.Poly1305.X86.nb s₀) s₁ ⟨0, rfl, hpos, hL₀⟩


/-! ## Constant time and satisfiability -/

/-- The taint analysis starts with the stack arguments public, and the word
holding `state` known to be the base address of the writable region. -/
def blocksτ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [128], argLen := 16, argBases := [(4, 0)] }

theorem blocks_wf₀ {s : State} (hp : VG.Proof.Poly1305.X86.BPre s) : VG.X86.Taint.Wf VG.Proof.Poly1305.X86.blocksτ₀ s := by
  have hst := hp.st_fit; have hs := hp.sp_fit
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨by simp only [hp.wr, VG.Proof.Poly1305.X86.blocksτ₀, List.forall₂_cons, Std.le_refl, List.Forall₂.nil, and_self], by simp only [hp.wr, List.pairwise_cons, List.not_mem_nil, false_implies, implies_true, List.Pairwise.nil, and_self], ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨hs, ?_⟩, ?_⟩
  · simp only [hp.wr, List.mem_singleton]
    rintro r rfl; simp only [BitVec.toNat_setWidth]; omega_using [hst]
  · simp only [hp.wr, List.mem_singleton]
    rintro r rfl
    exact VG.X86.Taint.frame_disjoint (n := 12) (by omega_using [hs]) hp.ret_st hp.arg_st
  · intro p hp'
    simp only [VG.Proof.Poly1305.X86.blocksτ₀, List.mem_singleton] at hp'
    subst hp'
    refine ⟨by decide, ?_⟩
    simp only [addr, BitVec.add_zero, Taint.region, hp.wr, arg, argAddr, Nat.mul_zero, Nat.add_zero, BitVec.ofNat_eq_ofNat, List.getD_eq_getElem?_getD, List.length_cons, List.length_nil, Nat.zero_add, Nat.lt_add_one, getElem?_pos, List.getElem_cons_zero, Option.getD_some]

theorem argMem_eq {s₁ s₂ : State} {n : Nat} (h₁ : (s₁.gpr .esp).toNat + n ≤ 2 ^ 32)
    (h₂ : (s₂.gpr .esp).toNat + n ≤ 2 ^ 32) (ha : ∀ i, 4 + 4 * i < n → arg s₁ i = arg s₂ i) {k : Nat}
    (h4 : 4 ≤ k) (hk : k < n) :
    s₁.mem (VG.X86.Taint.argByte s₁ k) = s₂.mem (VG.X86.Taint.argByte s₂ k) := by
  rw [VG.X86.Taint.argByte_eq h₁ h4 hk, VG.X86.Taint.argByte_eq h₂ h4 hk,
    Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by decide))]
  exact congrArg _ (ha _ (by omega_using [h4, hk]))

theorem blocks_agree₀ {s₁ s₂ : State} (h₁ : Proof.Poly1305.blocksX86.pre s₁)
    (h₂ : Proof.Poly1305.blocksX86.pre s₂) (hpub : Proof.Poly1305.blocksX86.pub s₁ s₂) :
    VG.X86.Taint.Agree VG.Proof.Poly1305.X86.blocksτ₀ s₁ s₂ := by
  obtain ⟨hesp, a0, a1, a2⟩ := hpub
  have hp₁ := BPre.of _ h₁; have hp₂ := BPre.of _ h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, VG.Proof.Poly1305.X86.blocks_wf₀ hp₁, VG.Proof.Poly1305.X86.blocks_wf₀ hp₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => (Nat.zero_add k).symm ▸ VG.Proof.Poly1305.X86.argMem_eq hp₁.sp_fit hp₂.sp_fit (fun i hi => ?_) h4 hk⟩
  · simp only [VG.Proof.Poly1305.X86.blocksτ₀, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]; simp only [VG.Proof.Poly1305.X86.stp, a0]
  · have : i = 0 ∨ i = 1 ∨ i = 2 := by omega_using [hi]
    rcases this with rfl | rfl | rfl
    exacts [a0, a1, a2]

/-- Memory holding the arguments `0x1000, 0x2000, 0` at `0x4004`. -/
def blocksSatMem : Mem := fun a => if a = 0x4005 then 0x10 else if a = 0x4009 then 0x20 else 0

/-- A state satisfying the precondition (with no blocks). -/
def blocksSat : State where
  gpr r := match r with
    | .esp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := VG.Proof.Poly1305.X86.blocksSatMem
  rd := [⟨0x2000, 0⟩, ⟨0x4004, 12⟩]
  wr := [⟨0x1000, 128⟩]

theorem blocks_ok (s : State) (hs : Proof.Poly1305.blocksX86.pre s) :
    ∃ t s', Exec isa blocks s t s' ∧ abiPreserved s s' ∧ Proof.Poly1305.blocksX86.post s s' :=
  VG.Proof.Poly1305.X86.blocks_correct (BPre.of s hs)

theorem blocks_ct : ConstantTime isa Proof.Poly1305.blocksX86.pre Proof.Poly1305.blocksX86.pub
    blocks :=
  VG.Taint.constantTime (A := taint) VG.Proof.Poly1305.X86.blocksτ₀ (fun _ _ h₁ h₂ hp => VG.Proof.Poly1305.X86.blocks_agree₀ h₁ h₂ hp)
    (by taint_decide)

theorem blocks_verified :
    Verified X86.target Impl.Poly1305.X86.blocks (Spec.Poly1305.blocksContract X86.abi) :=
  Verified.of_correct VG.Proof.Poly1305.X86.blocks_ok VG.Proof.Poly1305.X86.blocks_ct (by
    have a0 : arg VG.Proof.Poly1305.X86.blocksSat 0 = 0x1000 := by decide
    have a1 : arg VG.Proof.Poly1305.X86.blocksSat 1 = 0x2000 := by decide
    have a2 : arg VG.Proof.Poly1305.X86.blocksSat 2 = 0 := by decide
    have e : argAddr VG.Proof.Poly1305.X86.blocksSat 0 = 0x4004 := by decide
    have esp : blocksSat.gpr .esp = 0x4000 := rfl
    sig_implies [Spec.Poly1305.blocksContract, Spec.Poly1305.blocksSig, Proof.Poly1305.blocksX86,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [a0, a1, a2, e, esp] using Proof.Poly1305.X86.blocksSat)

end VG.Proof.Poly1305.X86

end

end

/- Proofs formerly in `VerifiedGarbage.Proof.Poly1305.X86.Buffer`. -/
section

/-!
# Poly1305 on x86 (32-bit): the buffer

The buffer (bytes 56–71 of the state, words 14 to 17), bytes copied into it,
absorbing it as a block, and what `update` and `finalize` share: the number of
bytes buffered, from `count`.
-/

namespace VG.Proof.Poly1305.X86

open VG VG.X86 VG.Impl.Poly1305.X86
open VG.Spec.Poly1305 (P leNum bytesAt Repr Buffered)

/-! ## Addresses -/

/-- The buffer's address, and its region. -/
abbrev bq (st : BitVec 32) : Addr := addr st 56
abbrev bfR (st : BitVec 32) : Region := VG.Proof.Poly1305.X86.sub st 56 16

theorem bq_eq {st : BitVec 32} (hfit : st.toNat + 128 ≤ 2 ^ 32) : VG.Proof.Poly1305.X86.bq st = st.setWidth 64 + 56 := by
  rw [VG.Proof.Poly1305.X86.bq, addr_eq (by omega_using [hfit])]; rfl

/-- Byte `k` of the buffer. -/
theorem bufB_eq {st : BitVec 32} (hfit : st.toNat + 128 ≤ 2 ^ 32) {k : Nat} (hk : k ≤ 16) :
    addr st (56 + k) = VG.Proof.Poly1305.X86.bq st + BitVec.ofNat 64 k := by
  rw [VG.Proof.Poly1305.X86.bq, addr_eq (by omega_using [hfit, hk]), addr_eq (by omega_using [hfit]), BitVec.add_assoc, ← BitVec.ofNat_add]

/-- The address `[x + 56]`, for `x = st + k`. -/
theorem addr_buf {st : BitVec 32} (hfit : st.toNat + 128 ≤ 2 ^ 32) {k : Nat} (hk : k ≤ 16) :
    addr (st + BitVec.ofNat 32 k) 56 = VG.Proof.Poly1305.X86.bq st + BitVec.ofNat 64 k := by
  rw [← VG.Proof.Poly1305.X86.bufB_eq hfit hk]
  simp only [addr]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm]

theorem bfR_contains {d n : Nat} (st : BitVec 32) (h : d + n ≤ 16) :
    (VG.Proof.Poly1305.X86.bfR st).Contains (VG.Proof.Poly1305.X86.bq st + BitVec.ofNat 64 d) n := by
  exact Offset.contains_base _ h (by omega_using [h])

theorem bfR_sub {st : BitVec 32} (hfit : st.toNat + 128 ≤ 2 ^ 32) : Region.Sub (VG.Proof.Poly1305.X86.bfR st) (VG.Proof.Poly1305.X86.sR st) :=
  fun _ ha => (VG.Proof.Poly1305.X86.sR_contains hfit (d := 56) (n := 16) (by decide) (by decide)).byte (by
    simp only [Region.Contains] at ha; omega_using [ha])

/-- The words outside the buffer, after writes only to it. -/
theorem words_bf {st : BitVec 32} (hfit : st.toNat + 128 ≤ 2 ^ 32) {m m' : Mem} (hf : Frame [VG.Proof.Poly1305.X86.bfR st] m m')
    {k : Nat} (hk : k < 32) (h : k < 14 ∨ 18 ≤ k) : VG.Proof.Poly1305.X86.words m' st k = VG.Proof.Poly1305.X86.words m st k := by
  show VG.Proof.Poly1305.X86.wv _ _ _ = VG.Proof.Poly1305.X86.wv _ _ _
  rw [VG.Proof.Poly1305.X86.wv, VG.Proof.Poly1305.X86.wv, VG.Proof.Poly1305.X86.wd_frame hf (by
    simp only [List.mem_singleton]; rintro r rfl
    exact VG.Proof.Poly1305.X86.sub_disj (by omega_using [hfit, hk]) (by omega_using [hfit]) (by omega_using [hk, h]))]

/-- The first `n` bytes of the buffer, where its words are unchanged. -/
theorem bytes_words {st : BitVec 32} (hfit : st.toNat + 128 ≤ 2 ^ 32) {m m' : Mem}
    (h : ∀ k, 14 ≤ k → k < 18 → VG.Proof.Poly1305.X86.words m' st k = VG.Proof.Poly1305.X86.words m st k) {n : Nat} (hn : n ≤ 16) :
    bytesAt m' (VG.Proof.Poly1305.X86.bq st) n = bytesAt m (VG.Proof.Poly1305.X86.bq st) n := by
  have e : bytesAt m' (VG.Proof.Poly1305.X86.bq st) (4 * 4) = bytesAt m (VG.Proof.Poly1305.X86.bq st) (4 * 4) :=
    VG.Proof.Poly1305.X86.bytesAt_congr_words fun k hk => BitVec.eq_of_toNat_eq (by
      have := h (14 + k) (by omega_using [hk]) (by omega_using [hk])
      simp only [VG.Proof.Poly1305.X86.words, VG.Proof.Poly1305.X86.wv, VG.Proof.Poly1305.X86.wd] at this
      rw [VG.Proof.Poly1305.X86.bq, addr_eq (by omega_using [hfit]), VG.Proof.Poly1305.X86.add_ofNat_add, ← addr_eq (by omega_using [hfit, hk]), show 56 + 4 * k = 4 * (14 + k) by omega_using []]
      exact this)
  have t : ∀ m'' : Mem, bytesAt m'' (VG.Proof.Poly1305.X86.bq st) n = (bytesAt m'' (VG.Proof.Poly1305.X86.bq st) (4 * 4)).take n := fun m'' => by
    rw [show 4 * 4 = n + (16 - n) by omega_using [hn], Poly1305.bytesAt_add, List.take_left' (Poly1305.length_bytesAt _ _ _)]
  rw [t, t, e]

/-- The buffer's words, as `absorbAt .edi 56` reads them. -/
theorem buf_ea {st : BitVec 32} (k : Nat) :
    addr st (56 + 4 * k) = addr (st + BitVec.ofNat 32 56) (4 * k) := by
  simp only [addr]; rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-- The buffer's value as a block: its four words, as `absorbAt .edi 56` reads
them. -/
theorem buf_value {st : BitVec 32} (hfit : st.toNat + 128 ≤ 2 ^ 32) (m : Mem) (pad : Nat) :
    VG.Proof.Poly1305.X86.blkv m (st + BitVec.ofNat 32 56) pad = leNum (bytesAt m (VG.Proof.Poly1305.X86.bq st) 16) + 2 ^ 128 * pad := by
  have hw : ∀ k < 4, VG.Proof.Poly1305.X86.wv m (st + BitVec.ofNat 32 56) (4 * k) = VG.Proof.Poly1305.X86.w32 m (VG.Proof.Poly1305.X86.bq st) k := fun k hk => by
    simp only [VG.Proof.Poly1305.X86.wv, VG.Proof.Poly1305.X86.wd, VG.Proof.Poly1305.X86.w32]
    rw [← VG.Proof.Poly1305.X86.buf_ea, VG.Proof.Poly1305.X86.bufB_eq hfit (by omega_using [hk])]
  rw [VG.Proof.Poly1305.X86.leNum_bytesAt_16, ← hw 0 (by decide), ← hw 1 (by decide), ← hw 2 (by decide), ← hw 3 (by decide)]

/-! ## The number of bytes buffered -/

theorem and15 (x : BitVec 32) : x &&& 15 = BitVec.ofNat 32 (x.toNat % 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (15 : BitVec 32).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := x.toNat % 16) (by omega_using [])]

theorem count_mod (s : State) : (Proof.Poly1305.countX86 s).toNat % 16 = (arg s 1).toNat % 16 := by
  simp only [Proof.Poly1305.countX86]
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (arg s 1).isLt, Nat.shiftLeft_eq]
  omega_using []

section
variable (s₀ : State)
/-- The number of bytes buffered, `count mod 16`. -/
abbrev kb : Nat := (arg s₀ 1).toNat % 16
/-- The bytes buffered. -/
abbrev Bf : List Byte := bytesAt s₀.mem (VG.Proof.Poly1305.X86.bq (VG.Proof.Poly1305.X86.stp s₀)) (VG.Proof.Poly1305.X86.kb s₀)
end

theorem kb_lt (s₀ : State) : VG.Proof.Poly1305.X86.kb s₀ < 16 := Nat.mod_lt _ (by decide)

/-- The length of a message of `count` bytes, modulo 16. -/
theorem count_mod16 {count : BitVec 64} {n : Nat} (h : count = BitVec.ofNat 64 n) :
    count.toNat % 16 = n % 16 := by
  rw [h, BitVec.toNat_ofNat]; omega_using []

/-- A state representing a message of `count` bytes (modulo 16): its whole
blocks, and the bytes buffered. -/
theorem buffered_split {s₀ : State} (hfit : (VG.Proof.Poly1305.X86.stp s₀).toNat + 128 ≤ 2 ^ 32) {key msg : List Byte}
    (h : Buffered s₀.mem ((VG.Proof.Poly1305.X86.stp s₀).setWidth 64) key msg)
    (hc : (Proof.Poly1305.countX86 s₀).toNat % 16 = msg.length % 16) :
    ∃ W, msg = W ++ VG.Proof.Poly1305.X86.Bf s₀ ∧ Repr s₀.mem ((VG.Proof.Poly1305.X86.stp s₀).setWidth 64) key W := by
  obtain ⟨W, B, rfl, hr, -, hBb⟩ := Buffered.split h
  have hk : VG.Proof.Poly1305.X86.kb s₀ = (W ++ B).length % 16 := by
    rw [VG.Proof.Poly1305.X86.kb, ← VG.Proof.Poly1305.X86.count_mod, hc]
  refine ⟨W, ?_, hr⟩
  rw [VG.Proof.Poly1305.X86.Bf, hk, VG.Proof.Poly1305.X86.bq_eq hfit, hBb]

theorem eq16_beq {a : Nat} (ha : a ≤ 16) : (BitVec.ofNat 32 a - 16 == 0) = decide (a = 16) := by
  by_cases h : a = 16
  · subst h; rfl
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    have := congrArg BitVec.toNat h'
    rw [show (0 : BitVec 32).toNat = 0 from rfl] at this
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at this
    rw [show (16 : BitVec 32).toNat = 16 from rfl, Nat.mod_eq_of_lt (a := a) (by omega_using [ha, this])] at this
    omega_using [ha, h, this]

/-! ## What holds throughout `update` and `finalize` -/

/-- What holds throughout, with the words `F` of `setup`. -/
structure UCommon (s₀ : State) (F : Nat → Nat) (s : State) : Prop where
  ctx : VG.Proof.Poly1305.X86.Ctx (VG.Proof.Poly1305.X86.stp s₀) s
  esp : s.gpr .esp = s₀.gpr .esp
  frame : Frame [VG.Proof.Poly1305.X86.sR (VG.Proof.Poly1305.X86.stp s₀)] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ k < 32, k ∉ VG.Proof.Poly1305.X86.hS → (k < 14 ∨ 18 ≤ k) → VG.Proof.Poly1305.X86.words s.mem (VG.Proof.Poly1305.X86.stp s₀) k = F k

theorem UCommon.regs {s₀ s s' : State} {F : Nat → Nat} (h : VG.Proof.Poly1305.X86.UCommon s₀ F s) (hedi : s'.gpr .edi = s.gpr .edi)
    (hesp : s'.gpr .esp = s.gpr .esp) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    VG.Proof.Poly1305.X86.UCommon s₀ F s' :=
  ⟨h.ctx.keep hedi hwr, hesp.trans h.esp, hm ▸ h.frame, hrd.trans h.rd, hwr.trans h.wr,
    fun k hk hS h' => hm ▸ h.keep k hk hS h'⟩

/-- Writing the buffer keeps what holds throughout. -/
theorem UCommon.buf {s₀ s s' : State} {F : Nat → Nat} (h : VG.Proof.Poly1305.X86.UCommon s₀ F s) (hedi : s'.gpr .edi = s.gpr .edi)
    (hesp : s'.gpr .esp = s.gpr .esp) (hf : Frame [VG.Proof.Poly1305.X86.bfR (VG.Proof.Poly1305.X86.stp s₀)] s.mem s'.mem) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hfit : (VG.Proof.Poly1305.X86.stp s₀).toNat + 128 ≤ 2 ^ 32) : VG.Proof.Poly1305.X86.UCommon s₀ F s' :=
  ⟨h.ctx.keep hedi hwr, hesp.trans h.esp,
    h.frame.trans (hf.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, VG.Proof.Poly1305.X86.bfR_sub hfit⟩),
    hrd.trans h.rd, hwr.trans h.wr, fun k hk hS h' => (VG.Proof.Poly1305.X86.words_bf hfit hf hk h').trans (h.keep k hk hS h')⟩

/-- The accumulator in the state's words is that of the message on entry
followed by the whole blocks `X`. -/
def Acc (s₀ : State) (X : List Byte) (m : Mem) : Prop :=
  VG.Proof.Poly1305.X86.A0 s₀ < P → VG.Proof.Poly1305.X86.words m (VG.Proof.Poly1305.X86.stp s₀) 4 ≤ 4 ∧
    VG.Proof.Poly1305.X86.hw5 (VG.Proof.Poly1305.X86.words m (VG.Proof.Poly1305.X86.stp s₀)) % P = Poly1305.absorbAll (VG.Proof.Poly1305.X86.Rn s₀) (VG.Proof.Poly1305.X86.A0 s₀) X % P

theorem Acc.words {s₀ : State} {X : List Byte} {m m' : Mem} (h : VG.Proof.Poly1305.X86.Acc s₀ X m)
    (hk : ∀ k < 5, VG.Proof.Poly1305.X86.words m' (VG.Proof.Poly1305.X86.stp s₀) k = VG.Proof.Poly1305.X86.words m (VG.Proof.Poly1305.X86.stp s₀) k) : VG.Proof.Poly1305.X86.Acc s₀ X m' := fun hA => by
  obtain ⟨h4, hv⟩ := h hA
  refine ⟨by rw [hk 4 (by decide)]; exact h4, ?_⟩
  simp only [VG.Proof.Poly1305.X86.hw5, hk 0 (by decide), hk 1 (by decide), hk 2 (by decide), hk 3 (by decide), hk 4 (by decide)]
  exact hv

/-! ## Copying bytes into the buffer -/

/-- The copy loop's body. -/
def copyBody : List Instr :=
  [.movzx8 .ecx (at_ .esi 0), .store8 (at_ .edx 56) .cl, .alu .add .esi (.imm 1),
    .alu .add .edx (.imm 1), .alu .sub .eax (.imm 1)]

theorem copyIn_eq : copyIn = .loop (.block VG.Proof.Poly1305.X86.copyBody) .ne := rfl

/-- While copying the `n` bytes at `src`, as in the memory `m₀`, to the buffer
of the state at `st` from byte `j0` on, from the state `sI`: after `j` bytes. -/
structure CopyInv (sI : State) (st : BitVec 32) (m₀ : Mem) (src : BitVec 32) (j0 n j : Nat) (s : State) :
    Prop where
  j_le : j ≤ n
  esi : s.gpr .esi = src + BitVec.ofNat 32 j
  edx : s.gpr .edx = st + BitVec.ofNat 32 (j0 + j)
  eax : s.gpr .eax = BitVec.ofNat 32 (n - j)
  keep : ∀ r, r ≠ .esi → r ≠ .edx → r ≠ .eax → r ≠ .ecx → s.gpr r = sI.gpr r
  rd : s.rd = sI.rd
  wr : s.wr = sI.wr
  mem : s.mem = Poly1305.writeBytes sI.mem (VG.Proof.Poly1305.X86.bq st + BitVec.ofNat 64 j0)
    ((bytesAt m₀ (src.setWidth 64) n).take j)

/-- What copying needs of the source: its bytes are readable, not in the
buffer, and as in `m₀`. -/
def SrcOk (sI : State) (st : BitVec 32) (m₀ : Mem) (src : BitVec 32) (n : Nat) : Prop :=
  src.toNat + n ≤ 2 ^ 32 ∧ ∀ i < n, InRegions (sI.rd ++ sI.wr) (addr src i) 1 ∧
    ¬ (VG.Proof.Poly1305.X86.bfR st).Contains (addr src i) 1 ∧ sI.mem (addr src i) = m₀ (addr src i)

theorem ofNat32_pred {k : Nat} (h : 1 ≤ k) (hk : k < 2 ^ 32) :
    BitVec.ofNat 32 k - 1 = BitVec.ofNat 32 (k - 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [show (1 : BitVec 32).toNat = 1 from rfl]
  omega_using [h, hk]

theorem copy_step {sI : State} {st : BitVec 32} {m₀ : Mem} {src : BitVec 32} {j0 n : Nat}
    (hfit : st.toNat + 128 ≤ 2 ^ 32) (hj0 : j0 + n ≤ 16) (hw : VG.Proof.Poly1305.X86.sR st ∈ sI.wr) (hs : VG.Proof.Poly1305.X86.SrcOk sI st m₀ src n)
    {j : Nat} (hj : j < n) {s : State} (h : VG.Proof.Poly1305.X86.CopyInv sI st m₀ src j0 n j s) :
    WP isa (.block VG.Proof.Poly1305.X86.copyBody) s fun s' =>
      VG.Proof.Poly1305.X86.CopyInv sI st m₀ src j0 n (j + 1) s' ∧ s'.zf = some (decide (n - (j + 1) = 0)) := by
  obtain ⟨hsf, hsrc⟩ := hs
  obtain ⟨hin, hnb, hm₀⟩ := hsrc j hj
  have hxs : (bytesAt m₀ (src.setWidth 64) n).length = n := Poly1305.length_bytesAt _ _ _
  have hq : (VG.Proof.Poly1305.X86.bfR st).Contains (VG.Proof.Poly1305.X86.bq st + BitVec.ofNat 64 j0) ((bytesAt m₀ (src.setWidth 64) n).take j).length := by
    rw [List.length_take]
    exact VG.Proof.Poly1305.X86.bfR_contains st (by omega_using [hj0, hj, hxs])
  -- The byte read.
  have hbyte : s.mem (addr src j) = m₀ (addr src j) := by
    rw [h.mem, ← hm₀]
    exact Poly1305.writeBytes_frame _ _ _ hq _ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hnb
  refine VG.Proof.Poly1305.X86.wp_movzx8 (d := .ecx) (a := addr src j)
    (by rw [VG.Proof.Poly1305.X86.ea_at, h.esi]; simp only [addr]; rw [BitVec.add_zero]) (by rw [h.rd, h.wr]; exact hin)
    fun s₁ u₁ => ?_
  refine VG.Proof.Poly1305.X86.wp_store8 (r := .cl) (a := VG.Proof.Poly1305.X86.bq st + BitVec.ofNat 64 (j0 + j))
    (by rw [VG.Proof.Poly1305.X86.ea_at, u₁.other _ (by decide), h.edx, VG.Proof.Poly1305.X86.addr_buf hfit (by omega_using [hj0, hj, hxs])])
    (by rw [u₁.wr, h.wr]; exact ⟨_, hw, (VG.Proof.Poly1305.X86.bfR_sub hfit) _ (VG.Proof.Poly1305.X86.bfR_contains st (d := j0 + j) (n := 1) (by omega_using [hj0, hj, hxs]))⟩) fun s₂ m₂ => ?_
  refine VG.Proof.Poly1305.X86.wp_addx (VG.Proof.Poly1305.X86.readSrc_imm _ _) fun s₃ u₃ _ => VG.Proof.Poly1305.X86.wp_addx (VG.Proof.Poly1305.X86.readSrc_imm _ _) fun s₄ u₄ _ => ?_
  refine VG.Proof.Poly1305.X86.wp_subx (VG.Proof.Poly1305.X86.readSrc_imm _ _) fun s₅ u₅ hz₅ => WP.block_nil ?_
  have g : ∀ r, r ≠ .eax → r ≠ .edx → r ≠ .esi → r ≠ .ecx → s₅.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 => by rw [u₅.other r h1, u₄.other r h2, u₃.other r h3, m₂.gpr, u₁.other r h4]
  have heax : s₅.gpr .eax = BitVec.ofNat 32 (n - (j + 1)) := by
    rw [u₅.gpr, u₄.other .eax (by decide), u₃.other .eax (by decide), m₂.gpr, u₁.other .eax (by decide), h.eax,
      VG.Proof.Poly1305.X86.ofNat32_pred (by omega_using [hj, hxs]) (by omega_using [hj0, hj, hxs]), Nat.sub_sub]
  refine ⟨⟨by omega_using [hj, hxs], ?_, ?_, heax, fun r h1 h2 h3 h4 => ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [u₅.other .esi (by decide), u₄.other .esi (by decide), u₃.gpr, m₂.gpr, u₁.other .esi (by decide), h.esi,
      BitVec.add_assoc, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ← BitVec.ofNat_add]
  · rw [u₅.other .edx (by decide), u₄.gpr, u₃.other .edx (by decide), m₂.gpr, u₁.other .edx (by decide), h.edx,
      BitVec.add_assoc, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ← BitVec.ofNat_add, Nat.add_assoc]
  · rw [g r h3 h2 h1 h4, h.keep r h1 h2 h3 h4]
  · rw [u₅.rd, u₄.rd, u₃.rd, m₂.rd, u₁.rd, h.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, m₂.wr, u₁.wr, h.wr]
  · have hj' : j < (bytesAt m₀ (src.setWidth 64) n).length := by omega_using [hj, hxs]
    have hl : ((bytesAt m₀ (src.setWidth 64) n).take j).length = j := by
      rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj')]
    have ea : VG.Proof.Poly1305.X86.bq st + BitVec.ofNat 64 (j0 + j) =
        VG.Proof.Poly1305.X86.bq st + BitVec.ofNat 64 j0 + BitVec.ofNat 64 ((bytesAt m₀ (src.setWidth 64) n).take j).length := by
      rw [hl, BitVec.add_assoc, ← BitVec.ofNat_add]
    have haddr : addr src j = src.setWidth 64 + BitVec.ofNat 64 j := addr_eq (by omega_using [hj, hsf, hxs, hl])
    have hv : (BitVec.setWidth 32 (s.mem (addr src j))).setWidth 8 = (bytesAt m₀ (src.setWidth 64) n)[j] := by
      rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq, hbyte, haddr]; simp [bytesAt]
    rw [u₅.mem, u₄.mem, u₃.mem, m₂.mem, show Reg8.cl.reg = Reg.ecx from rfl, u₁.gpr, hv, ea, u₁.mem, h.mem, List.take_add_one,
      List.getElem?_eq_getElem hj', Option.toList_some, Poly1305.writeBytes_snoc _ _ _ _ (by omega_using [hj0, hj, hxs, hl])]
  · rw [hz₅, u₄.other .eax (by decide), u₃.other .eax (by decide), m₂.gpr, u₁.other .eax (by decide), h.eax,
      VG.Proof.Poly1305.X86.ofNat32_pred (by omega_using [hj, hxs]) (by omega_using [hj0, hj, hxs]), VG.Proof.Poly1305.X86.ofNat32_beq_zero (by omega_using [hj0, hj, hxs]), show n - j - 1 = n - (j + 1) by omega_using []]

theorem copy_ok {sI : State} {st : BitVec 32} {m₀ : Mem} {src : BitVec 32} {j0 n : Nat}
    (hfit : st.toNat + 128 ≤ 2 ^ 32) (hj0 : j0 + n ≤ 16) (hn : 0 < n) (hw : VG.Proof.Poly1305.X86.sR st ∈ sI.wr)
    (hs : VG.Proof.Poly1305.X86.SrcOk sI st m₀ src n) (hesi : sI.gpr .esi = src) (hedx : sI.gpr .edx = st + BitVec.ofNat 32 j0)
    (heax : sI.gpr .eax = BitVec.ofNat 32 n) :
    WP isa copyIn sI (VG.Proof.Poly1305.X86.CopyInv sI st m₀ src j0 n n) := by
  have h₀ : VG.Proof.Poly1305.X86.CopyInv sI st m₀ src j0 n 0 sI :=
    ⟨by omega_using [hn], by rw [hesi]; simp, by rw [hedx, Nat.add_zero], by rw [heax, Nat.sub_zero], fun _ _ _ _ _ => rfl, rfl, rfl,
      by rw [List.take_zero, Poly1305.writeBytes_nil]⟩
  rw [VG.Proof.Poly1305.X86.copyIn_eq]
  refine WP.loop (M := isa) (fun k s => ∃ j, k = n - j ∧ j < n ∧ VG.Proof.Poly1305.X86.CopyInv sI st m₀ src j0 n j s)
    ?_ n sI ⟨0, rfl, hn, h₀⟩
  rintro k s ⟨j, rfl, hj, hc⟩
  refine WP.mono (VG.Proof.Poly1305.X86.copy_step hfit hj0 hw hs hj hc) fun s' ⟨hc', hz⟩ => ?_
  by_cases hl : n - (j + 1) = 0
  · refine .inl ⟨by simp [eval, hz, hl], ?_⟩
    rwa [show j + 1 = n by omega_using [hj, hl]] at hc'
  · exact .inr ⟨by simp [eval, hz, hl], _, by omega_using [hj], j + 1, rfl, by omega_using [hj, hl], hc'⟩

/-- After copying: the buffer's first `j0` bytes and the `n` bytes copied. -/
theorem CopyInv.buf {sI : State} {st : BitVec 32} {m₀ : Mem} {src : BitVec 32} {j0 n : Nat} (hj0 : j0 + n ≤ 16)
    {s : State} (h : VG.Proof.Poly1305.X86.CopyInv sI st m₀ src j0 n n s) :
    bytesAt s.mem (VG.Proof.Poly1305.X86.bq st) (j0 + n) = bytesAt sI.mem (VG.Proof.Poly1305.X86.bq st) j0 ++ bytesAt m₀ (src.setWidth 64) n := by
  have hxs : (bytesAt m₀ (src.setWidth 64) n).length = n := Poly1305.length_bytesAt _ _ _
  have e := Poly1305.bytesAt_writeBytes sI.mem (VG.Proof.Poly1305.X86.bq st) j0 (bytesAt m₀ (src.setWidth 64) n) (by omega_using [hj0, hxs])
  rw [hxs] at e
  rw [h.mem, List.take_of_length_le (by omega_using [hxs])]
  exact e

theorem CopyInv.frame {sI : State} {st : BitVec 32} {m₀ : Mem} {src : BitVec 32} {j0 n : Nat}
    (hj0 : j0 + n ≤ 16) {s : State} (h : VG.Proof.Poly1305.X86.CopyInv sI st m₀ src j0 n n s) :
    Frame [VG.Proof.Poly1305.X86.bfR st] sI.mem s.mem := by
  have hxs : (bytesAt m₀ (src.setWidth 64) n).length = n := Poly1305.length_bytesAt _ _ _
  rw [h.mem, List.take_of_length_le (by omega_using [hxs])]
  refine Poly1305.writeBytes_frame _ _ _ ?_
  rw [hxs]
  exact VG.Proof.Poly1305.X86.bfR_contains st hj0

end VG.Proof.Poly1305.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Poly1305.X86.Finalize`. -/
section

/-!
# Poly1305 on x86 (32-bit): `finalize`
-/

namespace VG.Proof.Poly1305.X86

open VG VG.X86 VG.Impl.Poly1305.X86
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr Buffered leBytes mac)

/-! ## The precondition -/

section
variable (s₀ : State)
abbrev op : BitVec 32 := arg s₀ 3
abbrev oR : Region := ⟨(VG.Proof.Poly1305.X86.op s₀).setWidth 64, 16⟩
abbrev fsR : Region := ⟨(arg s₀ 4).setWidth 64, 128⟩
end

structure FPre (s₀ : State) : Prop where
  rd : s₀.rd = [⟨argAddr s₀ 0, 20⟩]
  wr : s₀.wr = [VG.Proof.Poly1305.X86.sR (VG.Proof.Poly1305.X86.stp s₀), VG.Proof.Poly1305.X86.oR s₀, VG.Proof.Poly1305.X86.fsR s₀]
  st_o : (VG.Proof.Poly1305.X86.sR (VG.Proof.Poly1305.X86.stp s₀)).Disjoint (VG.Proof.Poly1305.X86.oR s₀)
  st_sc : (VG.Proof.Poly1305.X86.sR (VG.Proof.Poly1305.X86.stp s₀)).Disjoint (VG.Proof.Poly1305.X86.fsR s₀)
  o_sc : (VG.Proof.Poly1305.X86.oR s₀).Disjoint (VG.Proof.Poly1305.X86.fsR s₀)
  arg_st : Region.Disjoint ⟨argAddr s₀ 0, 20⟩ (VG.Proof.Poly1305.X86.sR (VG.Proof.Poly1305.X86.stp s₀))
  arg_o : Region.Disjoint ⟨argAddr s₀ 0, 20⟩ (VG.Proof.Poly1305.X86.oR s₀)
  arg_sc : Region.Disjoint ⟨argAddr s₀ 0, 20⟩ (VG.Proof.Poly1305.X86.fsR s₀)
  ret_st : (VG.Proof.Poly1305.X86.retR s₀).Disjoint (VG.Proof.Poly1305.X86.sR (VG.Proof.Poly1305.X86.stp s₀))
  ret_o : (VG.Proof.Poly1305.X86.retR s₀).Disjoint (VG.Proof.Poly1305.X86.oR s₀)
  ret_sc : (VG.Proof.Poly1305.X86.retR s₀).Disjoint (VG.Proof.Poly1305.X86.fsR s₀)
  st_fit : (VG.Proof.Poly1305.X86.stp s₀).toNat + 128 ≤ 2 ^ 32
  o_fit : (VG.Proof.Poly1305.X86.op s₀).toNat + 16 ≤ 2 ^ 32
  sc_fit : (arg s₀ 4).toNat + 128 ≤ 2 ^ 32
  sp_fit : (s₀.gpr .esp).toNat + 24 ≤ 2 ^ 32

theorem FPre.of (s₀ : State) (h : Proof.Poly1305.finalizeX86.pre s₀) : VG.Proof.Poly1305.X86.FPre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩

namespace FPre
variable {s₀ : State} (hp : VG.Proof.Poly1305.X86.FPre s₀)
include hp

theorem argIn {i : Nat} (hi : i < 5) : InRegions (s₀.rd ++ s₀.wr) (addr (s₀.gpr .esp) (4 + 4 * i)) 4 :=
  ⟨⟨argAddr s₀ 0, 20⟩, by rw [hp.rd]; simp, VG.Proof.Poly1305.X86.arg_contains (n := 20) (by have := hp.sp_fit; omega_using [this])
    (by omega_using [hi])⟩

/-- An argument, in memory the code has written only in the state and `out`. -/
theorem arg_same {m : Mem} (hf : Frame [VG.Proof.Poly1305.X86.sR (VG.Proof.Poly1305.X86.stp s₀), VG.Proof.Poly1305.X86.oR s₀] s₀.mem m) {i : Nat} (hi : i < 5) :
    m.readW (addr (s₀.gpr .esp) (4 + 4 * i)) 32 = arg s₀ i :=
  hf.readW (VG.Proof.Poly1305.X86.arg_contains (n := 20) (by have := hp.sp_fit; omega_using [this]) (by omega_using [hi]))
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl)
        <;> [exact hp.arg_st; exact hp.arg_o]) (by decide)

theorem st_in : VG.Proof.Poly1305.X86.sR (VG.Proof.Poly1305.X86.stp s₀) ∈ s₀.wr := by rw [hp.wr]; exact List.mem_cons_self

theorem o_in : VG.Proof.Poly1305.X86.oR s₀ ∈ s₀.wr := by rw [hp.wr]; simp

end FPre

/-! ## Prologue -/

/-- After the prologue, with the words `F` of `setup`. -/
structure F0 (s₀ : State) (F : Nat → Nat) (s : State) : Prop extends VG.Proof.Poly1305.X86.UCommon s₀ F s where
  buf : bytesAt s.mem (VG.Proof.Poly1305.X86.bq (VG.Proof.Poly1305.X86.stp s₀)) (VG.Proof.Poly1305.X86.kb s₀) = VG.Proof.Poly1305.X86.Bf s₀
  acc : VG.Proof.Poly1305.X86.Acc s₀ [] s.mem

theorem fprologue_ok {s₀ : State} (hp : VG.Proof.Poly1305.X86.FPre s₀) :
    WP isa (.block (setup ++ ([.mov .edx (.mem (at_ .esp 8)), .alu .and .edx (.imm 15),
      .alu .test .edx (.reg .edx)] : List Instr))) s₀ fun s => ∃ F, VG.Proof.Poly1305.X86.SetupF s₀ F ∧ VG.Proof.Poly1305.X86.F0 s₀ F s ∧
        s.gpr .edx = BitVec.ofNat 32 (VG.Proof.Poly1305.X86.kb s₀) ∧
        s.zf = some (BitVec.ofNat 32 (VG.Proof.Poly1305.X86.kb s₀) &&& BitVec.ofNat 32 (VG.Proof.Poly1305.X86.kb s₀) == 0) := by
  have hfit := hp.st_fit
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86.setup_ok (VG.Proof.Poly1305.X86.arg0_eq s₀) (hp.argIn (i := 0) (by decide)) hfit hp.st_in)
    fun s₁ ⟨F, A₁, c₁, hF, sv, co⟩ => ?_)
  have esp₁ := A₁.gpr .esp (by decide)
  have hF' := SetupF.of hF sv co
  have hf₁ : Frame [VG.Proof.Poly1305.X86.sR (VG.Proof.Poly1305.X86.stp s₀), VG.Proof.Poly1305.X86.oR s₀] s₀.mem s₁.mem := A₁.frame.mono (by simp)
  refine VG.Proof.Poly1305.X86.wp_movm (a := addr (s₀.gpr .esp) (4 + 4 * 1)) (by rw [VG.Proof.Poly1305.X86.ea_at, esp₁])
    (by rw [A₁.rd, A₁.wr]; exact hp.argIn (by decide)) fun s₂ u₂ _ => ?_
  refine VG.Proof.Poly1305.X86.wp_andx (VG.Proof.Poly1305.X86.readSrc_imm _ _) fun s₃ u₃ => VG.Proof.Poly1305.X86.wp_test fun s₄ k₄ z₄ => WP.block_nil ?_
  have hm : s₄.mem = s₁.mem := by rw [k₄.2.1, u₃.mem, u₂.mem]
  have hedx₃ : s₃.gpr .edx = BitVec.ofNat 32 (VG.Proof.Poly1305.X86.kb s₀) := by
    rw [u₃.gpr, u₂.gpr, hp.arg_same hf₁ (i := 1) (by decide), VG.Proof.Poly1305.X86.and15]
  have hw : ∀ k < 32, VG.Proof.Poly1305.X86.words s₄.mem (VG.Proof.Poly1305.X86.stp s₀) k = F k := fun k hk => by rw [hm]; exact A₁.words k hk
  refine ⟨F, hF', ⟨⟨c₁.keep (by rw [k₄.1 _ (by simp), u₃.other _ (by decide), u₂.other _ (by decide)])
      (by rw [k₄.2.2.2, u₃.wr, u₂.wr]), ?_, by rw [hm]; exact A₁.frame,
      by rw [k₄.2.2.1, u₃.rd, u₂.rd, A₁.rd], by rw [k₄.2.2.2, u₃.wr, u₂.wr, A₁.wr],
      fun k hk _ _ => hw k hk⟩, ?_, fun hA => ?_⟩, by rw [k₄.1 _ (by simp), hedx₃], by rw [z₄, hedx₃]⟩
  · rw [k₄.1 _ (by simp), u₃.other _ (by decide), u₂.other _ (by decide), esp₁]
  · refine VG.Proof.Poly1305.X86.bytes_words hfit (fun k h₁ h₂ => ?_) (Nat.le_of_lt (VG.Proof.Poly1305.X86.kb_lt s₀))
    rw [hw k (by omega_using [h₁, h₂]), hF'.low k (by omega_using [h₂]) (by omega_using [h₁, h₂])]
  · exact VG.Proof.Poly1305.X86.acc_entry hfit hF' (fun k hk => hw k (by omega_using [hk])) hA

/-! ## Padding the buffer in place -/

/-- The padded block: the buffered bytes, `0x01`, zeros. -/
def padded (s₀ : State) (k : Nat) : Byte :=
  if k < VG.Proof.Poly1305.X86.kb s₀ then (VG.Proof.Poly1305.X86.Bf s₀).getD k 0 else if k = VG.Proof.Poly1305.X86.kb s₀ then 1 else 0

/-- The buffer's bytes are `f k`. -/
def BufHas (m : Mem) (st : BitVec 32) (f : Nat → Byte) : Prop :=
  ∀ k < 16, m (VG.Proof.Poly1305.X86.bq st + BitVec.ofNat 64 k) = f k

theorem bytesAt_buf {m : Mem} {st : BitVec 32} {f : Nat → Byte} (h : VG.Proof.Poly1305.X86.BufHas m st f) :
    bytesAt m (VG.Proof.Poly1305.X86.bq st) 16 = (List.range 16).map f := by
  simp only [bytesAt]
  exact List.map_congr_left fun k hk => h k (List.mem_range.mp hk)

theorem bq_ne {st : BitVec 32} {j k : Nat} (hj : j < 16) (hk : k < 16) (h : j ≠ k) :
    VG.Proof.Poly1305.X86.bq st + BitVec.ofNat 64 j ≠ VG.Proof.Poly1305.X86.bq st + BitVec.ofNat 64 k := by
  intro he
  have := congrArg BitVec.toNat he
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
  have := (VG.Proof.Poly1305.X86.bq st).isLt
  omega

/-- The buffered bytes in the memory the prologue leaves. -/
theorem F0.byte {s₀ : State} {F : Nat → Nat} {s : State} (h : VG.Proof.Poly1305.X86.F0 s₀ F s) {k : Nat} (hk : k < VG.Proof.Poly1305.X86.kb s₀) :
    s.mem (VG.Proof.Poly1305.X86.bq (VG.Proof.Poly1305.X86.stp s₀) + BitVec.ofNat 64 k) = (VG.Proof.Poly1305.X86.Bf s₀).getD k 0 := by
  rw [← h.buf]
  simp [bytesAt, List.getD_eq_getElem?_getD, hk]

/-- The zero loop's invariant, before byte `j`, from the state `s₁` after the
prologue. -/
structure ZeroInv (s₀ s₁ : State) (j : Nat) (s : State) : Prop where
  j_le : VG.Proof.Poly1305.X86.kb s₀ ≤ j ∧ j ≤ 16
  ecx : s.gpr .ecx = VG.Proof.Poly1305.X86.stp s₀ + BitVec.ofNat 32 j
  edx : s.gpr .edx = BitVec.ofNat 32 j
  eax : s.gpr .eax = 0
  keep : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s.gpr r = s₁.gpr r
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  frame : Frame [VG.Proof.Poly1305.X86.bfR (VG.Proof.Poly1305.X86.stp s₀)] s₁.mem s.mem
  buf : VG.Proof.Poly1305.X86.BufHas s.mem (VG.Proof.Poly1305.X86.stp s₀) fun k =>
    if k < VG.Proof.Poly1305.X86.kb s₀ then (VG.Proof.Poly1305.X86.Bf s₀).getD k 0 else if k < j then 0 else s₁.mem (VG.Proof.Poly1305.X86.bq (VG.Proof.Poly1305.X86.stp s₀) + BitVec.ofNat 64 k)

theorem zinit_ok {s₀ : State} {F : Nat → Nat} {s₁ : State} (h₁ : VG.Proof.Poly1305.X86.F0 s₀ F s₁)
    (hedx : s₁.gpr .edx = BitVec.ofNat 32 (VG.Proof.Poly1305.X86.kb s₀)) :
    WP isa (.block [.mov .eax (.imm 0), .mov .ecx (.reg .edx), .alu .add .ecx (.reg .edi)]) s₁
      (VG.Proof.Poly1305.X86.ZeroInv s₀ s₁ (VG.Proof.Poly1305.X86.kb s₀)) := by
  refine VG.Proof.Poly1305.X86.wp_movi fun s₂ u₂ _ => VG.Proof.Poly1305.X86.wp_mov fun s₃ u₃ _ => VG.Proof.Poly1305.X86.wp_addx (VG.Proof.Poly1305.X86.readSrc_reg _ _) fun s₄ u₄ _ =>
    WP.block_nil ⟨⟨(Nat.le_refl _), Nat.le_of_lt (VG.Proof.Poly1305.X86.kb_lt s₀)⟩, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, by rw [u₄.rd, u₃.rd, u₂.rd],
      by rw [u₄.wr, u₃.wr, u₂.wr], by rw [u₄.mem, u₃.mem, u₂.mem]; exact Frame.refl _ _, fun k hk => ?_⟩
  · rw [u₄.gpr, u₃.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₂.other _ (by decide), hedx,
      h₁.ctx.edi, BitVec.add_comm]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), hedx]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
  · rw [u₄.other r h2, u₃.other r h2, u₂.other r h1]
  · rw [u₄.mem, u₃.mem, u₂.mem]
    by_cases hkf : k < VG.Proof.Poly1305.X86.kb s₀
    · simp only [hkf, ite_true]; exact h₁.byte hkf
    · simp only [hkf, ite_false]

theorem zero_step {s₀ : State} (hp : VG.Proof.Poly1305.X86.FPre s₀) {F : Nat → Nat} {s₁ : State} (h₁ : VG.Proof.Poly1305.X86.F0 s₀ F s₁) {j : Nat}
    (hj : j < 16) {s : State} (h : VG.Proof.Poly1305.X86.ZeroInv s₀ s₁ j s) :
    WP isa (.block [.store8 (at_ .ecx 56) .al, .alu .add .ecx (.imm 1), .alu .add .edx (.imm 1),
      .alu .cmp .edx (.imm 16)]) s fun s' => VG.Proof.Poly1305.X86.ZeroInv s₀ s₁ (j + 1) s' ∧ s'.zf = some (decide (j + 1 = 16)) := by
  have hfit := hp.st_fit
  refine VG.Proof.Poly1305.X86.wp_store8 (r := .al) (a := VG.Proof.Poly1305.X86.bq (VG.Proof.Poly1305.X86.stp s₀) + BitVec.ofNat 64 j)
    (by rw [VG.Proof.Poly1305.X86.ea_at, h.ecx, VG.Proof.Poly1305.X86.addr_buf hfit (by omega_using [hj])])
    (by rw [h.wr, h₁.wr]; exact ⟨_, hp.st_in, VG.Proof.Poly1305.X86.bfR_sub hfit _ (VG.Proof.Poly1305.X86.bfR_contains _ (d := j) (n := 1) (by omega_using [hj]))⟩)
    fun s₂ m₂ => ?_
  refine VG.Proof.Poly1305.X86.wp_addx (VG.Proof.Poly1305.X86.readSrc_imm _ _) fun s₃ u₃ _ => VG.Proof.Poly1305.X86.wp_addx (VG.Proof.Poly1305.X86.readSrc_imm _ _) fun s₄ u₄ _ => ?_
  refine VG.Proof.Poly1305.X86.wp_cmpx (VG.Proof.Poly1305.X86.readSrc_imm _ _) fun s₅ k₅ z₅ _ => WP.block_nil ?_
  have hedx : s₄.gpr .edx = BitVec.ofNat 32 (j + 1) := by
    rw [u₄.gpr, u₃.other _ (by decide), m₂.gpr, h.edx, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      ← BitVec.ofNat_add]
  refine ⟨⟨⟨Nat.le_trans h.j_le.1 (Nat.le_succ _), by omega_using [hj]⟩, ?_, by rw [k₅.gpr', hedx], ?_,
      fun r h1 h2 h3 => ?_, by rw [k₅.2.2.1, u₄.rd, u₃.rd, m₂.rd, h.rd],
      by rw [k₅.2.2.2, u₄.wr, u₃.wr, m₂.wr, h.wr], ?_, fun k hk => ?_⟩, ?_⟩
  · rw [k₅.gpr', u₄.other _ (by decide), u₃.gpr, m₂.gpr, h.ecx, BitVec.add_assoc,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ← BitVec.ofNat_add]
  · rw [k₅.gpr', u₄.other _ (by decide), u₃.other _ (by decide), m₂.gpr, h.eax]
  · rw [k₅.1 r List.not_mem_nil, u₄.other r h3, u₃.other r h2, m₂.gpr, h.keep r h1 h2 h3]
  · rw [k₅.2.1, u₄.mem, u₃.mem, m₂.mem]
    exact h.frame.writeW (List.mem_singleton_self _) _ (VG.Proof.Poly1305.X86.bfR_contains _ (by omega_using [hj]))
  · rw [k₅.2.1, u₄.mem, u₃.mem, m₂.mem, Poly1305.writeW8_apply]
    by_cases hkj : k = j
    · subst hkj
      simp only [ite_true, show Reg8.al.reg = Reg.eax from rfl, h.eax,
        show ¬ k < VG.Proof.Poly1305.X86.kb s₀ by have := h.j_le.1; omega_using [this], show k < k + 1 by omega_using [], ite_false]
      rfl
    · simp only [VG.Proof.Poly1305.X86.bq_ne hk hj hkj, ite_false]
      rw [h.buf k hk]
      by_cases h1 : k < VG.Proof.Poly1305.X86.kb s₀
      · simp only [h1, ite_true]
      · simp only [h1, ite_false]
        by_cases h2 : k < j
        · simp only [h2, ite_true, show k < j + 1 by omega_using [h2]]
        · simp only [h2, ite_false, show ¬ k < j + 1 by omega_using [hkj, h2]]
  · rw [z₅, hedx, VG.Proof.Poly1305.X86.eq16_beq (by omega_using [hj])]

theorem zeroLoop_ok {s₀ : State} (hp : VG.Proof.Poly1305.X86.FPre s₀) {F : Nat → Nat} {s₁ : State} (h₁ : VG.Proof.Poly1305.X86.F0 s₀ F s₁) {s : State}
    (h : VG.Proof.Poly1305.X86.ZeroInv s₀ s₁ (VG.Proof.Poly1305.X86.kb s₀) s) : WP isa zeroLoop s (VG.Proof.Poly1305.X86.ZeroInv s₀ s₁ 16) := by
  have hk := VG.Proof.Poly1305.X86.kb_lt s₀
  refine WP.loop (M := isa) (fun n s => ∃ j, n = 16 - j ∧ j < 16 ∧ VG.Proof.Poly1305.X86.ZeroInv s₀ s₁ j s) ?_ _ s
    ⟨VG.Proof.Poly1305.X86.kb s₀, rfl, hk, h⟩
  rintro n s ⟨j, rfl, hj, hz⟩
  refine WP.mono (VG.Proof.Poly1305.X86.zero_step hp h₁ hj hz) fun s' ⟨h', hz'⟩ => ?_
  by_cases hl : j + 1 = 16
  · exact .inl ⟨by simp [eval, hz', hl], hl ▸ h'⟩
  · exact .inr ⟨by simp [eval, hz', hl], _, by omega_using [hj], j + 1, rfl, by omega_using [hj, hl], h'⟩

/-- After the `0x01` byte. -/
structure PInv (s₀ s₁ : State) (s : State) : Prop where
  keep : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s.gpr r = s₁.gpr r
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  frame : Frame [VG.Proof.Poly1305.X86.bfR (VG.Proof.Poly1305.X86.stp s₀)] s₁.mem s.mem
  buf : VG.Proof.Poly1305.X86.BufHas s.mem (VG.Proof.Poly1305.X86.stp s₀) (VG.Proof.Poly1305.X86.padded s₀)

theorem pad1_ok {s₀ : State} (hp : VG.Proof.Poly1305.X86.FPre s₀) {F : Nat → Nat} {s₁ : State} (h₁ : VG.Proof.Poly1305.X86.F0 s₀ F s₁) {s : State}
    (h : VG.Proof.Poly1305.X86.ZeroInv s₀ s₁ 16 s) :
    WP isa (.block [.mov .eax (.imm 1), .mov .ecx (.mem (at_ .esp 8)), .alu .and .ecx (.imm 15),
      .alu .add .ecx (.reg .edi), .store8 (at_ .ecx 56) .al]) s (VG.Proof.Poly1305.X86.PInv s₀ s₁) := by
  have hfit := hp.st_fit
  have hk := VG.Proof.Poly1305.X86.kb_lt s₀
  have hedi : s.gpr .edi = VG.Proof.Poly1305.X86.stp s₀ := by
    rw [h.keep _ (by decide) (by decide) (by decide), h₁.ctx.edi]
  have hesp : s.gpr .esp = s₀.gpr .esp := by
    rw [h.keep _ (by decide) (by decide) (by decide), h₁.esp]
  have hf : Frame [VG.Proof.Poly1305.X86.sR (VG.Proof.Poly1305.X86.stp s₀), VG.Proof.Poly1305.X86.oR s₀] s₀.mem s.mem :=
    (h₁.frame.trans (h.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, VG.Proof.Poly1305.X86.bfR_sub hfit⟩)).mono (by simp)
  refine VG.Proof.Poly1305.X86.wp_movi fun s₂ u₂ _ => ?_
  refine VG.Proof.Poly1305.X86.wp_movm (a := addr (s₀.gpr .esp) (4 + 4 * 1)) (by rw [VG.Proof.Poly1305.X86.ea_at, u₂.other _ (by decide), hesp])
    (by rw [u₂.rd, u₂.wr, h.rd, h.wr, h₁.rd, h₁.wr]; exact hp.argIn (by decide)) fun s₃ u₃ _ => ?_
  refine VG.Proof.Poly1305.X86.wp_andx (VG.Proof.Poly1305.X86.readSrc_imm _ _) fun s₄ u₄ => VG.Proof.Poly1305.X86.wp_addx (VG.Proof.Poly1305.X86.readSrc_reg _ _) fun s₅ u₅ _ => ?_
  have hecx : s₅.gpr .ecx = VG.Proof.Poly1305.X86.stp s₀ + BitVec.ofNat 32 (VG.Proof.Poly1305.X86.kb s₀) := by
    rw [u₅.gpr, u₄.gpr, u₃.gpr, u₂.mem, hp.arg_same hf (i := 1) (by decide), VG.Proof.Poly1305.X86.and15, u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), hedi, BitVec.add_comm]
  refine VG.Proof.Poly1305.X86.wp_store8 (r := .al) (a := VG.Proof.Poly1305.X86.bq (VG.Proof.Poly1305.X86.stp s₀) + BitVec.ofNat 64 (VG.Proof.Poly1305.X86.kb s₀))
    (by rw [VG.Proof.Poly1305.X86.ea_at, hecx, VG.Proof.Poly1305.X86.addr_buf hfit (by omega_using [hk])])
    (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, h.wr, h₁.wr]
        exact ⟨_, hp.st_in, VG.Proof.Poly1305.X86.bfR_sub hfit _ (VG.Proof.Poly1305.X86.bfR_contains _ (d := VG.Proof.Poly1305.X86.kb s₀) (n := 1) (by omega_using [hk]))⟩)
    fun s₆ m₆ => WP.block_nil ?_
  refine ⟨fun r h1 h2 h3 => ?_, by rw [m₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, h.rd],
    by rw [m₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, h.wr], ?_, fun k hk' => ?_⟩
  · rw [m₆.gpr, u₅.other r h2, u₄.other r h2, u₃.other r h2, u₂.other r h1, h.keep r h1 h2 h3]
  · rw [m₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
    exact h.frame.writeW (List.mem_singleton_self _) _ (VG.Proof.Poly1305.X86.bfR_contains _ (by omega_using [hk]))
  · rw [m₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, Poly1305.writeW8_apply,
      show Reg8.al.reg = Reg.eax from rfl, u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr]
    by_cases hkj : k = VG.Proof.Poly1305.X86.kb s₀
    · subst hkj
      simp only [ite_true, VG.Proof.Poly1305.X86.padded, Nat.lt_irrefl, ite_false]
      decide
    · simp only [VG.Proof.Poly1305.X86.bq_ne hk' hk hkj, ite_false]
      rw [h.buf k hk']
      by_cases h1 : k < VG.Proof.Poly1305.X86.kb s₀
      · simp only [h1, ite_true, VG.Proof.Poly1305.X86.padded]
      · simp only [h1, ite_false, hk', ite_true, VG.Proof.Poly1305.X86.padded, hkj]

/-- The padded block as a number: the buffered bytes with `0x01` appended. -/
theorem padded_value {s₀ : State} {m : Mem} (h : VG.Proof.Poly1305.X86.BufHas m (VG.Proof.Poly1305.X86.stp s₀) (VG.Proof.Poly1305.X86.padded s₀)) :
    leNum (bytesAt m (VG.Proof.Poly1305.X86.bq (VG.Proof.Poly1305.X86.stp s₀)) 16) = leNum (VG.Proof.Poly1305.X86.Bf s₀ ++ [0x01]) := by
  have hk := VG.Proof.Poly1305.X86.kb_lt s₀
  have hlen : (VG.Proof.Poly1305.X86.Bf s₀).length = VG.Proof.Poly1305.X86.kb s₀ := Poly1305.length_bytesAt _ _ _
  have hl : (List.range 16).map (VG.Proof.Poly1305.X86.padded s₀) = (VG.Proof.Poly1305.X86.Bf s₀ ++ [0x01]) ++ List.replicate (15 - VG.Proof.Poly1305.X86.kb s₀) 0 := by
    apply List.ext_getElem
    · simp [hlen]; omega_using [hk, hlen]
    · intro k h₁ h₂
      simp only [List.getElem_map, List.getElem_range]
      rcases Nat.lt_trichotomy k (VG.Proof.Poly1305.X86.kb s₀) with hk' | rfl | hk'
      · rw [List.getElem_append_left (by simp [hlen]; omega_using [hlen, hk']), List.getElem_append_left (by omega_using [hlen, hk'])]
        simp only [VG.Proof.Poly1305.X86.padded, hk', ite_true]
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show k < (VG.Proof.Poly1305.X86.Bf s₀).length by omega_using [hlen, hk'])]
      · rw [List.getElem_append_left (by simp [hlen]), List.getElem_append_right (by omega_using [hlen])]
        simp [VG.Proof.Poly1305.X86.padded, hlen]
      · rw [List.getElem_append_right (by simp [hlen]; omega_using [hlen, hk'])]
        simp [VG.Proof.Poly1305.X86.padded, show ¬ k < VG.Proof.Poly1305.X86.kb s₀ by omega_using [hlen, hk'], show k ≠ VG.Proof.Poly1305.X86.kb s₀ by omega_using [hlen, hk']]
  rw [VG.Proof.Poly1305.X86.bytesAt_buf h, hl, Poly1305.leNum_append _ (List.replicate _ _), Poly1305.leNum_replicate_zero,
    Nat.mul_zero, Nat.add_zero]

/-- After the buffered bytes (if any) are absorbed. -/
structure TInv (s₀ : State) (F : Nat → Nat) (s : State) : Prop extends VG.Proof.Poly1305.X86.UCommon s₀ F s where
  acc : VG.Proof.Poly1305.X86.Acc s₀ (VG.Proof.Poly1305.X86.Bf s₀) s.mem

theorem Bf_nil {s₀ : State} (h : VG.Proof.Poly1305.X86.kb s₀ = 0) : VG.Proof.Poly1305.X86.Bf s₀ = [] := by
  simp [VG.Proof.Poly1305.X86.Bf, bytesAt, h]

theorem lastBlock_ok {s₀ : State} (hp : VG.Proof.Poly1305.X86.FPre s₀) {F : Nat → Nat} (hF : VG.Proof.Poly1305.X86.SetupF s₀ F) {s₁ : State}
    (h₁ : VG.Proof.Poly1305.X86.F0 s₀ F s₁) (hedx : s₁.gpr .edx = BitVec.ofNat 32 (VG.Proof.Poly1305.X86.kb s₀)) (hpos : 0 < VG.Proof.Poly1305.X86.kb s₀) :
    WP isa lastBlock s₁ (VG.Proof.Poly1305.X86.TInv s₀ F) := by
  have hfit := hp.st_fit
  have hk := VG.Proof.Poly1305.X86.kb_lt s₀
  refine WP.seq (WP.mono (VG.Proof.Poly1305.X86.zinit_ok h₁ hedx) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Poly1305.X86.zeroLoop_ok hp h₁ h₂) fun s₃ h₃ => ?_)
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86.pad1_ok hp h₁ h₃) fun s₄ h₄ => ?_)
  have hU₄ : VG.Proof.Poly1305.X86.UCommon s₀ F s₄ := h₁.toUCommon.buf (h₄.keep _ (by decide) (by decide) (by decide))
    (h₄.keep _ (by decide) (by decide) (by decide)) h₄.frame h₄.rd h₄.wr hfit
  have hacc₄ : VG.Proof.Poly1305.X86.Acc s₀ [] s₄.mem := h₁.acc.words fun k hk => VG.Proof.Poly1305.X86.words_bf hfit h₄.frame (by omega_using [hk]) (by omega_using [hk])
  have hc := hU₄.ctx
  refine WP.mono (VG.Proof.Poly1305.X86.absorbAtFull_ok hc (bp := VG.Proof.Poly1305.X86.stp s₀ + BitVec.ofNat 32 56) (VG.Proof.Poly1305.X86.absorbBuf_okList 0)
    (fun h => absurd h (by decide)) (by decide) (fun k _ => by rw [hc.edi, VG.Proof.Poly1305.X86.buf_ea])
    (fun k hk => by rw [← VG.Proof.Poly1305.X86.buf_ea]; exact hc.inRW (by omega_using [hk]) (by decide))
    (fun k _ => .inr (by rw [← VG.Proof.Poly1305.X86.buf_ea]; congr 1; omega_using [])) (by decide) (C := VG.Proof.Poly1305.X86.A0 s₀ < P)
    (fun hA => ⟨hF.coefs.congr fun k h₁' h₂' => hU₄.keep k (by omega_using [h₁', h₂']) (VG.Proof.Poly1305.X86.not_hS (.inl ⟨by omega_using [h₁', h₂'], h₂'⟩))
      (.inr h₁'), (hacc₄ hA).1⟩))
    fun s' ⟨S, ha⟩ => ?_
  refine ⟨⟨hc.keep (S.gpr _ (by decide)) S.wr, by rw [S.gpr _ (by decide)]; exact hU₄.esp,
    hU₄.frame.trans S.frame, by rw [S.rd]; exact hU₄.rd, by rw [S.wr]; exact hU₄.wr,
    fun k hk hS h' => (S.same k hk hS).trans (hU₄.keep k hk hS h')⟩, fun hA => ?_⟩
  obtain ⟨-, hv⟩ := hacc₄ hA
  obtain ⟨h4, hv'⟩ := ha hA
  refine ⟨h4, ?_⟩
  have hlen : (VG.Proof.Poly1305.X86.Bf s₀).length = VG.Proof.Poly1305.X86.kb s₀ := Poly1305.length_bytesAt _ _ _
  rw [Poly1305.absorbAll_nil] at hv
  rw [hv', VG.Proof.Poly1305.X86.buf_value hfit, VG.Proof.Poly1305.X86.padded_value h₄.buf, show (0 : BitVec 32).toNat = 0 from rfl, Nat.mul_zero,
    Nat.add_zero, VG.Proof.Poly1305.X86.mod_step hv, Poly1305.absorbAll_block (by omega_using [hpos, hk, hlen]) (by omega_using [hpos, hk, hlen])]

/-! ## Regions -/

/-- The bytes `[x + d, x + d + n)` of a region of `k` bytes at `x`. -/
theorem contains0 {x : BitVec 32} {k d n : Nat} (hx : x.toNat + k ≤ 2 ^ 32) (h : d + n ≤ k) (hn : 0 < n) :
    (⟨x.setWidth 64, k⟩ : Region).Contains (addr x d) n := by
  have := VG.Proof.Poly1305.X86.sub_contains (x := x) (a := 0) (k := k) (d := d) (n := n) (by omega_using [hx]) (by omega_using []) (by omega_using [h]) hn
  simpa [VG.Proof.Poly1305.X86.sub, addr] using this

theorem sub_sub0 {x : BitVec 32} {k d n : Nat} (hx : x.toNat + k ≤ 2 ^ 32) (h : d + n ≤ k) (hn : 0 < n) :
    Region.Sub (VG.Proof.Poly1305.X86.sub x d n) ⟨x.setWidth 64, k⟩ := fun a ha =>
  (VG.Proof.Poly1305.X86.contains0 hx h hn).byte (by simp only [Region.Contains] at ha; omega_using [ha])


/-- The words of the state, after writes only to a region disjoint from it. -/
theorem words_frame {m m' : Mem} {st o : BitVec 32} (hst : st.toNat + 128 ≤ 2 ^ 32)
    (hd : (VG.Proof.Poly1305.X86.sR st).Disjoint ⟨o.setWidth 64, 16⟩) (hf : Frame [⟨o.setWidth 64, 16⟩] m m') {k : Nat}
    (hk : k < 32) : VG.Proof.Poly1305.X86.words m' st k = VG.Proof.Poly1305.X86.words m st k := by
  show VG.Proof.Poly1305.X86.wv _ _ _ = VG.Proof.Poly1305.X86.wv _ _ _
  rw [VG.Proof.Poly1305.X86.wv, VG.Proof.Poly1305.X86.wv, VG.Proof.Poly1305.X86.wd_frame hf (by
    simp only [List.mem_singleton]; rintro r rfl; exact hd.sub_left (VG.Proof.Poly1305.X86.sub_sub0 hst (by omega_using [hk]) (by decide)))]

/-! ## After the last bytes -/

/-! ## The tag -/

theorem words_lt (m : Mem) (st : BitVec 32) (k : Nat) : VG.Proof.Poly1305.X86.words m st k < 2 ^ 32 := BitVec.isLt _

/-- Word `i` of `h` plus word `i` of `s`. -/
abbrev ta (m : Mem) (st : BitVec 32) (i : Nat) : Nat := VG.Proof.Poly1305.X86.words m st i + VG.Proof.Poly1305.X86.words m st (10 + i)

/-- The carry into word `k` of the tag. -/
def cs (a : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => (a k + VG.Proof.Poly1305.X86.cs a k) / 2 ^ 32

theorem cs_succ (a : Nat → Nat) (k : Nat) : VG.Proof.Poly1305.X86.cs a (k + 1) = (a k + VG.Proof.Poly1305.X86.cs a k) / 2 ^ 32 := rfl

theorem cs_le {a : Nat → Nat} (ha : ∀ i, a i < 2 ^ 33 - 1) : ∀ k, VG.Proof.Poly1305.X86.cs a k ≤ 1
  | 0 => Nat.zero_le _
  | k + 1 => by rw [VG.Proof.Poly1305.X86.cs_succ]; have := VG.Proof.Poly1305.X86.cs_le ha k; have := ha k; omega

/-- The words of the tag: those of `x + y` modulo `2¹²⁸`. -/
theorem tag_words (x y : Nat → Nat) {X : Nat}
    (hX : X % 2 ^ 128 = x 0 + 2 ^ 32 * x 1 + 2 ^ 64 * x 2 + 2 ^ 96 * x 3) {k : Nat} (hk : k < 4) :
    (x k + y k + VG.Proof.Poly1305.X86.cs (fun i => x i + y i) k) % 2 ^ 32 =
      (X + (y 0 + 2 ^ 32 * y 1 + 2 ^ 64 * y 2 + 2 ^ 96 * y 3)) / 2 ^ (32 * k) % 2 ^ 32 := by
  obtain ⟨a0, a1, a2, a3⟩ := VG.Proof.Poly1305.X86.addS_arith (x0 := x 0) (x1 := x 1) (x2 := x 2) (x3 := x 3) (s0 := y 0)
    (s1 := y 1) (s2 := y 2) (s3 := y 3) X _ hX rfl
  have c1 : VG.Proof.Poly1305.X86.cs (fun i => x i + y i) 1 = (x 0 + y 0) / 2 ^ 32 := rfl
  have c2 : VG.Proof.Poly1305.X86.cs (fun i => x i + y i) 2 = (x 1 + y 1 + (x 0 + y 0) / 2 ^ 32) / 2 ^ 32 := rfl
  have c3 : VG.Proof.Poly1305.X86.cs (fun i => x i + y i) 3 =
      (x 2 + y 2 + (x 1 + y 1 + (x 0 + y 0) / 2 ^ 32) / 2 ^ 32) / 2 ^ 32 := rfl
  rcases (by omega_using [hk] : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
  · rw [show VG.Proof.Poly1305.X86.cs (fun i => x i + y i) 0 = 0 from rfl, Nat.add_zero, Nat.mul_zero, Nat.pow_zero, Nat.div_one]
    exact a0
  · rw [c1]; exact a1
  · rw [c2]; exact a2
  · rw [c3]; exact a3

/-- The tag's words so far, from the state `s` before them. -/
structure TagInv (st o : BitVec 32) (s : State) (k : Nat) (s' : State) : Prop where
  gpr : ∀ r, r ≠ .eax → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [⟨o.setWidth 64, 16⟩] s.mem s'.mem
  out : ∀ i < k, VG.Proof.Poly1305.X86.wv s'.mem o (4 * i) = (VG.Proof.Poly1305.X86.ta s.mem st i + VG.Proof.Poly1305.X86.cs (VG.Proof.Poly1305.X86.ta s.mem st) i) % 2 ^ 32
  cf : 0 < k → ∃ c, s'.cf = some c ∧ c.toNat = VG.Proof.Poly1305.X86.cs (VG.Proof.Poly1305.X86.ta s.mem st) k

theorem tagWord_ok {st o : BitVec 32} {s₁ : State} (hc : VG.Proof.Poly1305.X86.Ctx st s₁) (ho : o.toNat + 16 ≤ 2 ^ 32)
    (hesi : s₁.gpr .esi = o) (hout : (⟨o.setWidth 64, 16⟩ : Region) ∈ s₁.wr)
    (hd : (VG.Proof.Poly1305.X86.sR st).Disjoint ⟨o.setWidth 64, 16⟩) {k : Nat} (hk : k < 4) {s : State}
    (h : VG.Proof.Poly1305.X86.TagInv st o s₁ k s) :
    WP isa (.block [.mov .eax (.mem (at_ .edi (hOff k))),
      .alu (if k = 0 then .add else .adc) .eax (.mem (at_ .edi (40 + 4 * k))),
      .store (at_ .esi (4 * k)) .eax]) s (VG.Proof.Poly1305.X86.TagInv st o s₁ (k + 1)) := by
  have hfit := hc.fit
  have hw : ∀ j < 32, VG.Proof.Poly1305.X86.words s.mem st j = VG.Proof.Poly1305.X86.words s₁.mem st j := fun j hj => VG.Proof.Poly1305.X86.words_frame hfit hd h.frame hj
  have edi : s.gpr .edi = st := by rw [h.gpr _ (by decide), hc.edi]
  have hta : ∀ i, VG.Proof.Poly1305.X86.ta s₁.mem st i < 2 ^ 33 - 1 := fun i => by
    have := VG.Proof.Poly1305.X86.words_lt s₁.mem st i; have := VG.Proof.Poly1305.X86.words_lt s₁.mem st (10 + i)
    show VG.Proof.Poly1305.X86.words s₁.mem st i + VG.Proof.Poly1305.X86.words s₁.mem st (10 + i) < _
    omega
  have hcs : VG.Proof.Poly1305.X86.cs (VG.Proof.Poly1305.X86.ta s₁.mem st) k ≤ 1 := VG.Proof.Poly1305.X86.cs_le hta k
  have htk := hta k
  refine VG.Proof.Poly1305.X86.wp_movm (a := addr st (4 * k)) (by rw [VG.Proof.Poly1305.X86.ea_at, edi]; rfl)
    (by rw [h.rd, h.wr]; exact hc.inRW (by omega_using [hk]) (by decide)) fun s₂ u₂ cf₂ => ?_
  have e₂ : (s₂.gpr .eax).toNat = VG.Proof.Poly1305.X86.words s₁.mem st k := by rw [u₂.gpr, ← hw k (by omega_using [hk])]; rfl
  have hx : readSrc s₂ (.mem (at_ .edi (40 + 4 * k))) = some (s.mem.readW (addr st (40 + 4 * k)) 32) := by
    rw [VG.Proof.Poly1305.X86.readSrc_mem (a := addr st (40 + 4 * k)) (by rw [VG.Proof.Poly1305.X86.ea_at, u₂.other _ (by decide), edi])
      (by rw [u₂.rd, u₂.wr, h.rd, h.wr]; exact hc.inRW (by omega_using [hk]) (by decide)), u₂.mem]
  have ex : (s.mem.readW (addr st (40 + 4 * k)) 32).toNat = VG.Proof.Poly1305.X86.words s₁.mem st (10 + k) := by
    rw [← hw (10 + k) (by omega_using [hk])]
    show _ = VG.Proof.Poly1305.X86.wv _ _ (4 * (10 + k))
    rw [show 4 * (10 + k) = 40 + 4 * k by omega_using []]
  have fin : ∀ (s₃ : State) (y : BitVec 32), VG.Proof.Poly1305.X86.Upd s₂ s₃ .eax y →
      y.toNat = (VG.Proof.Poly1305.X86.ta s₁.mem st k + VG.Proof.Poly1305.X86.cs (VG.Proof.Poly1305.X86.ta s₁.mem st) k) % 2 ^ 32 →
      s₃.cf = some (decide (2 ^ 32 ≤ VG.Proof.Poly1305.X86.ta s₁.mem st k + VG.Proof.Poly1305.X86.cs (VG.Proof.Poly1305.X86.ta s₁.mem st) k)) →
      WP isa (.block [.store (at_ .esi (4 * k)) .eax]) s₃ (VG.Proof.Poly1305.X86.TagInv st o s₁ (k + 1)) := by
    intro s₃ y u₃ hy cf₃
    refine VG.Proof.Poly1305.X86.wp_store (a := addr o (4 * k))
      (by rw [VG.Proof.Poly1305.X86.ea_at, u₃.other _ (by decide), u₂.other _ (by decide), h.gpr _ (by decide), hesi])
      (by rw [u₃.wr, u₂.wr, h.wr]; exact ⟨_, hout, VG.Proof.Poly1305.X86.contains0 ho (by omega_using [hk]) (by decide)⟩) fun s₄ u₄ =>
        WP.block_nil ⟨fun r hr => ?_, ?_, ?_, ?_, fun i hi => ?_, fun _ => ⟨_, by rw [u₄.cf]; exact cf₃, ?_⟩⟩
    · rw [u₄.gpr, u₃.other r hr, u₂.other r hr, h.gpr r hr]
    · rw [u₄.rd, u₃.rd, u₂.rd, h.rd]
    · rw [u₄.wr, u₃.wr, u₂.wr, h.wr]
    · rw [u₄.mem, u₃.mem, u₂.mem]
      exact h.frame.writeW (List.mem_singleton_self _) _ (VG.Proof.Poly1305.X86.contains0 ho (by omega_using [hk]) (by decide))
    · rw [u₄.mem, u₃.gpr, u₃.mem, u₂.mem]
      by_cases hik : i = k
      · subst hik; rw [VG.Proof.Poly1305.X86.wv, VG.Proof.Poly1305.X86.wd_write_self]; exact hy
      · rw [VG.Proof.Poly1305.X86.wv, VG.Proof.Poly1305.X86.wd_write_ne _ _ (by omega_using [ho, hk, hi]) (by omega_using [ho, hk]) (by omega_using [hi, hik])]; exact h.out i (by omega_using [hi, hik])
    · rw [VG.Proof.Poly1305.X86.carry_dec (by omega_using [hcs, htk, hy]), VG.Proof.Poly1305.X86.cs_succ]
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [ite_eq_left rfl]
    refine VG.Proof.Poly1305.X86.wp_addx hx fun s₃ u₃ cf₃ => fin s₃ _ u₃ ?_ ?_
    · rw [BitVec.toNat_add, e₂, ex]; rfl
    · rw [cf₃, e₂, ex]; rfl
  · rw [ite_eq_right (by omega_using [hk, hk0])]
    obtain ⟨c, hcf, hcv⟩ := h.cf hk0
    refine VG.Proof.Poly1305.X86.wp_adcx hx (by rw [cf₂, hcf]) fun s₃ u₃ cf₃ => fin s₃ _ u₃ ?_ ?_
    · rw [VG.Proof.Poly1305.X86.add3_toNat, e₂, ex, hcv]
    · rw [cf₃, e₂, ex, hcv]

/-- `addS`: the tag into `out`. -/
theorem addS_ok {st o : BitVec 32} {s : State} (hc : VG.Proof.Poly1305.X86.Ctx st s) (ho : o.toNat + 16 ≤ 2 ^ 32)
    (harg : s.mem.readW (addr (s.gpr .esp) 16) 32 = o)
    (hin : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 16) 4)
    (hout : (⟨o.setWidth 64, 16⟩ : Region) ∈ s.wr) (hd : (VG.Proof.Poly1305.X86.sR st).Disjoint ⟨o.setWidth 64, 16⟩) :
    WP isa (.block addS) s fun s' => (∀ r, r ≠ .eax → r ≠ .esi → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ Frame [⟨o.setWidth 64, 16⟩] s.mem s'.mem ∧
      ∀ i < 4, VG.Proof.Poly1305.X86.wv s'.mem o (4 * i) = (VG.Proof.Poly1305.X86.ta s.mem st i + VG.Proof.Poly1305.X86.cs (VG.Proof.Poly1305.X86.ta s.mem st) i) % 2 ^ 32 := by
  refine VG.Proof.Poly1305.X86.wp_movm (a := addr (s.gpr .esp) 16) (VG.Proof.Poly1305.X86.ea_at _ _ _) hin fun s₁ u₁ _ => ?_
  have c₁ : VG.Proof.Poly1305.X86.Ctx st s₁ := hc.keep (u₁.other _ (by decide)) u₁.wr
  have esi : s₁.gpr .esi = o := by rw [u₁.gpr, harg]
  have ind : ∀ n ≤ 4, WP isa (.block ((List.range n).flatMap fun k => [.mov .eax (.mem (at_ .edi (hOff k))),
      .alu (if k = 0 then .add else .adc) .eax (.mem (at_ .edi (40 + 4 * k))),
      .store (at_ .esi (4 * k)) .eax])) s₁ (VG.Proof.Poly1305.X86.TagInv st o s₁ n) := by
    intro n hn
    induction n with
    | zero => exact WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, Frame.refl _ _, fun i hi => absurd hi (by omega_using [hi]),
        fun h => absurd h (by decide)⟩
    | succ n ih =>
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      exact WP.block_append (WP.mono (ih (by omega_using [hn])) fun s' h' =>
        VG.Proof.Poly1305.X86.tagWord_ok c₁ ho esi (by rw [u₁.wr]; exact hout) hd (by omega_using [hn]) h')
  refine WP.mono (ind 4 (Nat.le_refl _)) fun s₂ h₂ =>
    ⟨fun r h₁ h₂' => ?_, by rw [h₂.rd, u₁.rd], by rw [h₂.wr, u₁.wr], ?_, fun i hi => ?_⟩
  · rw [h₂.gpr r h₁, u₁.other r h₂']
  · rw [← u₁.mem]; exact h₂.frame
  · rw [h₂.out i hi, u₁.mem]

/-! ## Epilogue -/

theorem fepilogue_ok {s₀ : State} (hp : VG.Proof.Poly1305.X86.FPre s₀) {F : Nat → Nat} (hF : VG.Proof.Poly1305.X86.SetupF s₀ F) {s : State}
    (hL : VG.Proof.Poly1305.X86.TInv s₀ F s) :
    WP isa (.block (reduce ++ addS ++ restore)) s
      fun s' => abiPreserved s₀ s' ∧ Proof.Poly1305.finalizeX86.post s₀ s' := by
  have hfit := hp.st_fit
  have ho := hp.o_fit
  refine WP.block_append (WP.block_append (WP.mono (VG.Proof.Poly1305.X86.reduceFull_ok hL.ctx) fun s₁ ⟨S₁, h₁⟩ => ?_))
  have c₁ := hL.ctx.keep (S₁.gpr _ (by decide)) S₁.wr
  have esp₁ : s₁.gpr .esp = s₀.gpr .esp := by rw [S₁.gpr _ (by decide), hL.esp]
  have hf₁ : Frame [VG.Proof.Poly1305.X86.sR (VG.Proof.Poly1305.X86.stp s₀), VG.Proof.Poly1305.X86.oR s₀] s₀.mem s₁.mem := (hL.frame.trans S₁.frame).mono (by simp)
  refine WP.mono (VG.Proof.Poly1305.X86.addS_ok c₁ ho (by rw [esp₁]; exact hp.arg_same hf₁ (i := 3) (by decide))
    (by rw [S₁.rd, S₁.wr, hL.rd, hL.wr, esp₁]; exact hp.argIn (i := 3) (by decide))
    (by rw [S₁.wr, hL.wr]; exact hp.o_in) hp.st_o) fun s₂ ⟨g₂, rd₂, wr₂, f₂, o₂⟩ => ?_
  have c₂ : VG.Proof.Poly1305.X86.Ctx (VG.Proof.Poly1305.X86.stp s₀) s₂ := c₁.keep (g₂ _ (by decide) (by decide)) wr₂
  refine WP.mono (VG.Proof.Poly1305.X86.restore_ok c₂) fun s₃ ⟨b₃, si₃, di₃, bp₃, sp₃, A₃⟩ => ?_
  -- Words of the state that neither the reduction nor the tag changes.
  have hk : ∀ k < 32, k ∉ VG.Proof.Poly1305.X86.hS → VG.Proof.Poly1305.X86.words s₂.mem (VG.Proof.Poly1305.X86.stp s₀) k = VG.Proof.Poly1305.X86.words s.mem (VG.Proof.Poly1305.X86.stp s₀) k := by
    intro k hk h₁'
    rw [VG.Proof.Poly1305.X86.words_frame hfit hp.st_o f₂ hk]
    exact S₁.same k hk h₁'
  have hframe : Frame [VG.Proof.Poly1305.X86.sR (VG.Proof.Poly1305.X86.stp s₀), VG.Proof.Poly1305.X86.oR s₀] s₀.mem s₃.mem :=
    hf₁.trans ((f₂.mono (by simp)).trans (A₃.frame.mono (by simp)))
  refine ⟨VG.Proof.Poly1305.X86.abi_of hF.saved ?_ ?_ ?_ ?_ ?_ ?_, fun key msg hbuf hcnt => ?_⟩
  · rw [b₃, hk 29 (by decide) (by decide), hL.keep 29 (by decide) (by decide) (by decide)]
  · rw [si₃, hk 30 (by decide) (by decide), hL.keep 30 (by decide) (by decide) (by decide)]
  · rw [di₃, hk 31 (by decide) (by decide), hL.keep 31 (by decide) (by decide) (by decide)]
  · rw [bp₃, hk 5 (by decide) (by decide), hL.keep 5 (by decide) (by decide) (by decide)]
  · rw [sp₃, g₂ _ (by decide) (by decide), esp₁]
  · refine hframe.readW (Region.contains_self _ _) ?_ (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    exacts [hp.ret_st, hp.ret_o]
  · obtain ⟨W, rfl, hrep⟩ := VG.Proof.Poly1305.X86.buffered_split hfit hbuf hcnt
    have hA := VG.Proof.Poly1305.X86.A0_lt hrep
    obtain ⟨hcl, hac⟩ := VG.Proof.Poly1305.X86.repr_acc hfit hrep
    obtain ⟨h4, hv⟩ := hL.acc hA
    obtain ⟨hr, -⟩ := h₁ h4
    -- `h`, reduced.
    have hX : VG.Proof.Poly1305.X86.hw5 (VG.Proof.Poly1305.X86.words s₁.mem (VG.Proof.Poly1305.X86.stp s₀)) = accumulate (clamp (leNum (key.take 16))) (W ++ VG.Proof.Poly1305.X86.Bf s₀) := by
      rw [hr, hv, hcl, Poly1305.accumulate_append hrep.1, hac, Nat.mod_eq_of_lt (Poly1305.absorbAll_lt hA _)]
    -- `s`, words 10 to 13 of the state.
    have e : ∀ k < 4, VG.Proof.Poly1305.X86.words s₁.mem (VG.Proof.Poly1305.X86.stp s₀) (10 + k) = VG.Proof.Poly1305.X86.wv s₀.mem (VG.Proof.Poly1305.X86.stp s₀) (24 + 16 + 4 * k) := by
      intro k hk
      rw [show VG.Proof.Poly1305.X86.words s₁.mem (VG.Proof.Poly1305.X86.stp s₀) (10 + k) = VG.Proof.Poly1305.X86.wv s₁.mem (VG.Proof.Poly1305.X86.stp s₀) (4 * (10 + k)) from rfl,
        S₁.same _ (by omega_using [hk]) (VG.Proof.Poly1305.X86.not_hS (.inl ⟨by omega_using [hk], by omega_using [hk]⟩))]
      have := (hL.keep (10 + k) (by omega_using [hk]) (VG.Proof.Poly1305.X86.not_hS (.inl ⟨by omega_using [hk], by omega_using [hk]⟩)) (by omega_using [hk])).trans
        (hF.low (10 + k) (by omega_using [hk]) (by omega_using [hk]))
      simp only [VG.Proof.Poly1305.X86.words] at this
      rw [this, show 4 * (10 + k) = 24 + 16 + 4 * k by omega_using []]
    have hSk : leNum ((key.drop 16).take 16) = VG.Proof.Poly1305.X86.words s₁.mem (VG.Proof.Poly1305.X86.stp s₀) (10 + 0) +
        2 ^ 32 * VG.Proof.Poly1305.X86.words s₁.mem (VG.Proof.Poly1305.X86.stp s₀) (10 + 1) + 2 ^ 64 * VG.Proof.Poly1305.X86.words s₁.mem (VG.Proof.Poly1305.X86.stp s₀) (10 + 2) +
        2 ^ 96 * VG.Proof.Poly1305.X86.words s₁.mem (VG.Proof.Poly1305.X86.stp s₀) (10 + 3) := by
      rw [← hrep.2.1, show bytesAt s₀.mem ((VG.Proof.Poly1305.X86.stp s₀).setWidth 64 + 24) 32 =
          bytesAt s₀.mem ((VG.Proof.Poly1305.X86.stp s₀).setWidth 64 + 24) (16 + 16) from rfl, Poly1305.bytesAt_add,
        List.drop_left' (Poly1305.length_bytesAt _ _ _),
        List.take_of_length_le (by rw [Poly1305.length_bytesAt]), VG.Proof.Poly1305.X86.leNum_bytesAt_16,
        show (24 : Addr) = BitVec.ofNat 64 24 from rfl, VG.Proof.Poly1305.X86.add_ofNat_add, VG.Proof.Poly1305.X86.w32_off hfit (by decide),
        VG.Proof.Poly1305.X86.w32_off hfit (by decide), VG.Proof.Poly1305.X86.w32_off hfit (by decide), VG.Proof.Poly1305.X86.w32_off hfit (by decide), e 0 (by decide),
        e 1 (by decide), e 2 (by decide), e 3 (by decide)]
    have hXm : VG.Proof.Poly1305.X86.hw5 (VG.Proof.Poly1305.X86.words s₁.mem (VG.Proof.Poly1305.X86.stp s₀)) % 2 ^ 128 = VG.Proof.Poly1305.X86.words s₁.mem (VG.Proof.Poly1305.X86.stp s₀) 0 +
        2 ^ 32 * VG.Proof.Poly1305.X86.words s₁.mem (VG.Proof.Poly1305.X86.stp s₀) 1 + 2 ^ 64 * VG.Proof.Poly1305.X86.words s₁.mem (VG.Proof.Poly1305.X86.stp s₀) 2 +
        2 ^ 96 * VG.Proof.Poly1305.X86.words s₁.mem (VG.Proof.Poly1305.X86.stp s₀) 3 := by
      have := VG.Proof.Poly1305.X86.words_lt s₁.mem (VG.Proof.Poly1305.X86.stp s₀) 0; have := VG.Proof.Poly1305.X86.words_lt s₁.mem (VG.Proof.Poly1305.X86.stp s₀) 1
      have := VG.Proof.Poly1305.X86.words_lt s₁.mem (VG.Proof.Poly1305.X86.stp s₀) 2; have := VG.Proof.Poly1305.X86.words_lt s₁.mem (VG.Proof.Poly1305.X86.stp s₀) 3
      simp only [VG.Proof.Poly1305.X86.hw5, VG.Proof.Poly1305.X86.val5]
      omega
    have hout : bytesAt s₃.mem ((VG.Proof.Poly1305.X86.op s₀).setWidth 64) 16 = bytesAt s₂.mem ((VG.Proof.Poly1305.X86.op s₀).setWidth 64) 16 :=
      Poly1305.bytesAt_frame A₃.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.st_o.symm) (by decide)
    rw [hout]
    show bytesAt s₂.mem ((VG.Proof.Poly1305.X86.op s₀).setWidth 64) 16 = leBytes 16
      (accumulate (clamp (leNum (key.take 16))) (W ++ VG.Proof.Poly1305.X86.Bf s₀) + leNum ((key.drop 16).take 16))
    rw [← hX, hSk]
    refine VG.Proof.Poly1305.X86.bytesAt_leBytes_16w _ _ _ fun k hk => ?_
    rw [show VG.Proof.Poly1305.X86.w32 s₂.mem ((VG.Proof.Poly1305.X86.op s₀).setWidth 64) k = VG.Proof.Poly1305.X86.wv s₂.mem (VG.Proof.Poly1305.X86.op s₀) (4 * k) by
      simp only [VG.Proof.Poly1305.X86.w32, VG.Proof.Poly1305.X86.wv, VG.Proof.Poly1305.X86.wd]; rw [addr_eq (by omega_using [ho, hk])], o₂ k hk]
    exact VG.Proof.Poly1305.X86.tag_words (fun i => VG.Proof.Poly1305.X86.words s₁.mem (VG.Proof.Poly1305.X86.stp s₀) i) (fun i => VG.Proof.Poly1305.X86.words s₁.mem (VG.Proof.Poly1305.X86.stp s₀) (10 + i)) hXm hk

/-! ## The whole function -/

theorem finalize_eq : finalize = .seq (.block (setup ++ ([.mov .edx (.mem (at_ .esp 8)),
    .alu .and .edx (.imm 15), .alu .test .edx (.reg .edx)] : List Instr)))
    (.seq (.ite .e (.block []) lastBlock) (.block (reduce ++ addS ++ restore))) := rfl

theorem finalize_correct {s₀ : State} (hp : VG.Proof.Poly1305.X86.FPre s₀) :
    WP isa finalize s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Poly1305.finalizeX86.post s₀ s' := by
  rw [VG.Proof.Poly1305.X86.finalize_eq]
  refine WP.seq (WP.mono (VG.Proof.Poly1305.X86.fprologue_ok hp) fun s₁ ⟨F, hF, h₁, hedx, hz⟩ => ?_)
  refine WP.seq (WP.mono (Q := VG.Proof.Poly1305.X86.TInv s₀ F) ?_ fun s₂ h₂ => VG.Proof.Poly1305.X86.fepilogue_ok hp hF h₂)
  refine WP.ite (BitVec.ofNat 32 (VG.Proof.Poly1305.X86.kb s₀) &&& BitVec.ofNat 32 (VG.Proof.Poly1305.X86.kb s₀) == 0) (by simp [eval, hz])
    (fun h => ?_) (fun h => ?_)
  · rw [BitVec.and_self, VG.Proof.Poly1305.X86.ofNat32_beq_zero (by have := VG.Proof.Poly1305.X86.kb_lt s₀; omega_using [this])] at h
    simp only [decide_eq_true_eq] at h
    exact WP.block_nil ⟨h₁.toUCommon, by rw [VG.Proof.Poly1305.X86.Bf_nil h]; exact h₁.acc⟩
  · rw [BitVec.and_self, VG.Proof.Poly1305.X86.ofNat32_beq_zero (by have := VG.Proof.Poly1305.X86.kb_lt s₀; omega_using [this])] at h
    simp only [decide_eq_false_iff_not] at h
    exact VG.Proof.Poly1305.X86.lastBlock_ok hp hF h₁ hedx (by omega_using [h])

/-! ## Constant time and satisfiability -/

/-- The taint analysis starts with the stack arguments public. -/
def finalizeτ₀ : VG.X86.Taint.T := { regs := .ofList [.esp], flags := false, argLen := 24 }

theorem finalize_wf₀ {s : State} (hp : VG.Proof.Poly1305.X86.FPre s) : VG.X86.Taint.Wf VG.Proof.Poly1305.X86.finalizeτ₀ s := by
  have hs := hp.sp_fit
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨by simp only [VG.Proof.Poly1305.X86.finalizeτ₀]; omega_using [hs], ?_⟩,
    fun _ h => (List.not_mem_nil h).elim⟩
  simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega_using [hs]) hp.ret_st hp.arg_st
  · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega_using [hs]) hp.ret_o hp.arg_o
  · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega_using [hs]) hp.ret_sc hp.arg_sc

theorem finalize_agree₀ {s₁ s₂ : State} (h₁ : Proof.Poly1305.finalizeX86.pre s₁)
    (h₂ : Proof.Poly1305.finalizeX86.pre s₂) (hpub : Proof.Poly1305.finalizeX86.pub s₁ s₂) :
    VG.X86.Taint.Agree VG.Proof.Poly1305.X86.finalizeτ₀ s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  have hp₁ := FPre.of _ h₁; have hp₂ := FPre.of _ h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h, VG.Proof.Poly1305.X86.finalize_wf₀ hp₁, VG.Proof.Poly1305.X86.finalize_wf₀ hp₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => (Nat.zero_add k).symm ▸ VG.Proof.Poly1305.X86.argMem_eq hp₁.sp_fit hp₂.sp_fit (fun i hi => ha i (by omega_using [hi]))
      h4 hk⟩
  simp only [VG.Proof.Poly1305.X86.finalizeτ₀, RegSet.mem_ofList, List.mem_singleton] at hr
  subst hr; exact hesp

/-- Memory holding the arguments `0x1000, 0, 0, 0x2000, 0x3000` at `0x4004`. -/
def finalizeSatMem : Mem := fun a =>
  if a = 0x4005 then 0x10 else if a = 0x4011 then 0x20 else if a = 0x4015 then 0x30 else 0

/-- A state satisfying the precondition. -/
def finalizeSat : State where
  gpr r := match r with
    | .esp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := VG.Proof.Poly1305.X86.finalizeSatMem
  rd := [⟨0x4004, 20⟩]
  wr := [⟨0x1000, 128⟩, ⟨0x2000, 16⟩, ⟨0x3000, 128⟩]

theorem finalize_ok (s : State) (hs : Proof.Poly1305.finalizeX86.pre s) :
    ∃ t s', Exec isa finalize s t s' ∧ abiPreserved s s' ∧ Proof.Poly1305.finalizeX86.post s s' :=
  VG.Proof.Poly1305.X86.finalize_correct (FPre.of s hs)

theorem finalize_ct : ConstantTime isa Proof.Poly1305.finalizeX86.pre Proof.Poly1305.finalizeX86.pub
    finalize :=
  VG.Taint.constantTime (A := taint) VG.Proof.Poly1305.X86.finalizeτ₀ (fun _ _ h₁ h₂ hp => VG.Proof.Poly1305.X86.finalize_agree₀ h₁ h₂ hp)
    (by taint_decide)

/-- The per-target contract of `finalize` only needs the length of the
message modulo 16. -/
theorem finalize_verified :
    Verified X86.target Impl.Poly1305.X86.finalize (Spec.Poly1305.finalizeScratchContract X86.abi) :=
  Verified.of_correct VG.Proof.Poly1305.X86.finalize_ok VG.Proof.Poly1305.X86.finalize_ct
    { pre := by
        sig_implies_pre [Spec.Poly1305.finalizeScratchContract, Spec.Poly1305.finalizeScratchSig, Spec.Poly1305.finalizePost,
          Proof.Poly1305.finalizeX86, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      post := by
        intro s s' _ h
        sig_eval [Spec.Poly1305.finalizeScratchContract, Spec.Poly1305.finalizeScratchSig, Spec.Poly1305.finalizePost, X86.abi, X86.argSlots,
          X86.argVal, X86.argBytes]
        intro key msg hb hc
        exact h key msg hb (Proof.Poly1305.X86.count_mod16 hc)
      pub := by
        sig_implies_pub [Spec.Poly1305.finalizeScratchContract, Spec.Poly1305.finalizeScratchSig, Spec.Poly1305.finalizePost,
          Proof.Poly1305.finalizeX86, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      sat := by
        have a0 : arg VG.Proof.Poly1305.X86.finalizeSat 0 = 0x1000 := by decide
        have a3 : arg VG.Proof.Poly1305.X86.finalizeSat 3 = 0x2000 := by decide
        have a4 : arg VG.Proof.Poly1305.X86.finalizeSat 4 = 0x3000 := by decide
        have e : argAddr VG.Proof.Poly1305.X86.finalizeSat 0 = 0x4004 := by decide
        have esp : finalizeSat.gpr .esp = 0x4000 := rfl
        sig_implies_sat [Spec.Poly1305.finalizeScratchContract, Spec.Poly1305.finalizeScratchSig, Spec.Poly1305.finalizePost,
          Proof.Poly1305.finalizeX86, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
          [a0, a3, a4, e, esp] using Proof.Poly1305.X86.finalizeSat }

end VG.Proof.Poly1305.X86

end
