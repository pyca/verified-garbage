import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Terms
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Lemmas
import VerifiedGarbage.Proof.Bignum.Amm52N

/-!
# RSA with AVX512_IFMA on x86-64, any size: the lanes of a step

With `R` registers per number, under `StepIn` (the lanes of the
roles hold the limbs `L p`, below `2⁶²`; the operands' limbs, `k₀` and the
limb `b p` in memory, below `2⁵²`; the zero register zero), role `k`'s lane
`t` after the step holds limb `k + R t` of `Amm52N.step (4 R)` (`hT_eval`).
-/

namespace VG.Proof.Bignum.X86_64.Ifma

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Impl.Rsa.X86_64.CrtIfma
open VG.Proof.Bignum.X86_64.AmmSym (ops lo_comm mad_lo mad_hi shr_ofNat add_ofNat G.eval)
open VG.Proof.X25519.X86_64.Ifma (mad52)

variable {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay}

/-- The machine before step `i`, for limbs `L p`, operand limbs `a p`,
modulus limbs `m p`, `k₀` `k p` and second-operand limb `b p`. -/
structure StepIn (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (s : State) (i : Nat) (L a m : Nat → Nat → Nat) (k b : Nat → Nat) : Prop where
  z : ∀ t < 4, qv s (vreg (zN l)) t = 0
  lanes : ∀ p < 2, ∀ kk < l.R, ∀ t < 4, qv s (vreg (regOf l p kk i)) t = BitVec.ofNat 64 (L p (kk + l.R * t))
  lt : ∀ p < 2, ∀ j < l.L, L p j < 2 ^ 62
  ina : ∀ p < 2, ∀ kk < l.R, ∀ t < 4,
    s.mem.readW (s.gpr .r8 + BitVec.ofNat 64 (l.D * p + 32 * kk + 8 * t)) 64 = BitVec.ofNat 64 (a p (kk + l.R * t))
  inm : ∀ p < 2, ∀ kk < l.R, ∀ t < 4,
    s.mem.readW (s.gpr .r10 + BitVec.ofNat 64 (l.D * p + oM + 32 * kk + 8 * t)) 64 =
      BitVec.ofNat 64 (m p (kk + l.R * t))
  ink : ∀ p < 2, ∀ t < 4,
    s.mem.readW (s.gpr .r10 + BitVec.ofNat 64 (l.D * p + l.oK0 + 8 * t)) 64 = BitVec.ofNat 64 (k p)
  inb : ∀ p < 2, s.mem.readW (s.gpr .r9 + BitVec.ofNat 64 (l.D * p + 32 * i)) 64 = BitVec.ofNat 64 (b p)
  alt : ∀ p < 2, ∀ j < l.L, a p j < 2 ^ 52
  mlt : ∀ p < 2, ∀ j < l.L, m p j < 2 ^ 52
  klt : ∀ p < 2, k p < 2 ^ 52
  blt : ∀ p < 2, b p < 2 ^ 52

/-- Limb `kk + R t` of lane `t` of role `kk` is one of the `4 R`. -/
theorem idx_lt {kk t : Nat} (hk : kk < l.R) (ht : t < 4) : kk + l.R * t < l.L := by
  have := Nat.mul_le_mul_left l.R (Nat.le_of_lt_succ ht)
  simp only [Lay.L]; omega

section
variable {s : State} {i : Nat} {L a m : Nat → Nat → Nat} {k b : Nat → Nat}

theorem bT_eval (h : StepIn l s i L a m k b) {p : Nat} (hp : p < 2) (t : Nat) :
    (bT l p i).eval s t = BitVec.ofNat 64 (b p) := by
  simp only [bT, T.eval, ite_true, G.eval]; exact h.inb p hp

theorem a1T_eval (h : StepIn l s i L a m k b) {p kk t : Nat} (hp : p < 2) (hk : kk < l.R) (ht : t < 4) :
    (a1T l p kk i).eval s t = BitVec.ofNat 64 (L p (kk + l.R * t) + lo (a p (kk + l.R * t)) (b p)) := by
  have hl := h.lt p hp (kk + l.R * t) (idx_lt hk ht)
  simp only [a1T, T.eval]
  rw [h.lanes p hp kk hk t ht, bT_eval h hp, h.ina p hp kk hk t ht, mad_lo (by omega)]

theorem uT_eval (h : StepIn l s i L a m k b) (hR : 2 ≤ l.R) {p : Nat} (hp : p < 2) (t : Nat) :
    (uT l p i).eval s t = BitVec.ofNat 64 (stepU (ops a m k p) (L p) (b p)) := by
  have hl := h.lt p hp 0 (by simp only [Lay.L]; omega)
  have := lo_lt (a p 0) (b p)
  simp only [uT, T.eval]
  rw [a1T_eval h hp (by omega) (by decide), show (0 : Nat) + l.R * 0 = 0 by omega,
    h.ink p hp 0 (by decide),
    show (0 : BitVec 64) = BitVec.ofNat 64 0 from rfl, mad_lo (by omega), Nat.zero_add, lo_comm]
  rfl

theorem a2T_eval0 (h : StepIn l s i L a m k b) (hR : 2 ≤ l.R) {p t : Nat} (hp : p < 2) (ht : t < 4) :
    (a2T l p 0 i).eval s t = BitVec.ofNat 64 (low (ops a m k p) (L p) (b p) (0 + l.R * t)) := by
  have hl := h.lt p hp (0 + l.R * t) (idx_lt (by omega) ht)
  have := lo_lt (a p (0 + l.R * t)) (b p)
  simp only [a2T, a1hT, ite_true, T.eval]
  rw [a1T_eval h hp (by omega) ht, uT_eval h hR hp, h.inm p hp 0 (by omega) t ht, mad_lo (by omega)]
  simp only [low, ops]

/-- Role `kk + 1` after the low halves: plus the high halves of role `kk` of `a b`. -/
theorem a2T_evalS (h : StepIn l s i L a m k b) (hR : 2 ≤ l.R) {p kk t : Nat} (hp : p < 2)
    (hk : kk + 1 < l.R) (ht : t < 4) :
    (a2T l p (kk + 1) i).eval s t =
      BitVec.ofNat 64 (low (ops a m k p) (L p) (b p) (kk + 1 + l.R * t) + hi (a p (kk + l.R * t)) (b p)) := by
  have hl := h.lt p hp (kk + 1 + l.R * t) (idx_lt hk ht)
  have := lo_lt (a p (kk + 1 + l.R * t)) (b p)
  have := hi_lt (a p (kk + l.R * t)) (b p)
  have := lo_lt (m p (kk + 1 + l.R * t)) (stepU (ops a m k p) (L p) (b p))
  simp only [a2T, a1hT, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel, T.eval]
  rw [a1T_eval h hp hk ht, bT_eval h hp, h.ina p hp kk (by omega) t ht, mad_hi (by omega), uT_eval h hR hp,
    h.inm p hp (kk + 1) hk t ht, mad_lo (by omega)]
  exact congrArg (BitVec.ofNat 64) (by simp only [low, ops]; omega)

theorem low_lt (h : StepIn l s i L a m k b) {p j : Nat} (hp : p < 2) (hj : j < l.L) :
    low (ops a m k p) (L p) (b p) j < 2 ^ 62 + 2 ^ 53 := by
  have := h.lt p hp j hj
  have := lo_lt (a p j) (b p)
  have := lo_lt (m p j) (stepU (ops a m k p) (L p) (b p))
  show L p j + lo (a p j) (b p) + lo (m p j) (stepU (ops a m k p) (L p) (b p)) < _
  omega

theorem cT_eval (h : StepIn l s i L a m k b) (hR : 2 ≤ l.R) {p t : Nat} (hp : p < 2) (ht : t < 4) :
    (cT l p i).eval s t =
      BitVec.ofNat 64 (if t = 0 then low (ops a m k p) (L p) (b p) 0 / 2 ^ 52 else 0) := by
  have h0 := low_lt h hp (j := 0) (by simp only [Lay.L]; omega)
  simp only [cT, T.eval]
  by_cases t0 : t = 0
  · subst t0
    simp only [ite_true]
    rw [a2T_eval0 h hR hp (by decide), show (0 : Nat) + l.R * 0 = 0 by omega, shr_ofNat (by omega)]
  · simp only [t0, ite_false]; rfl

/-- Role `kk` after the shift: for `kk < R - 1`, with the high halves of role `kk` of `a b`. -/
theorem nT_eval (h : StepIn l s i L a m k b) (hR : 2 ≤ l.R) {p kk t : Nat} (hp : p < 2) (hk : kk < l.R)
    (ht : t < 4) :
    (nT l p kk i).eval s t = BitVec.ofNat 64 (Amm52N.shifted l.L (low (ops a m k p) (L p) (b p)) (kk + l.R * t) +
      if kk = l.R - 1 then 0 else hi (a p (kk + l.R * t)) (b p)) := by
  have hRt := Nat.mul_le_mul_left l.R (Nat.le_of_lt_succ ht)
  by_cases hl : kk = l.R - 1
  · subst hl
    simp only [nT, ite_true, T.eval, Nat.add_zero]
    by_cases t3 : t + 1 < 4
    · simp only [t3, ite_true]
      rw [a2T_eval0 h hR hp t3]
      have := Nat.mul_le_mul_left l.R (show t ≤ 2 by omega)
      simp only [Amm52N.shifted, Lay.L, show l.R - 1 + l.R * t + 1 < 4 * l.R by omega,
        show l.R - 1 + l.R * t ≠ 0 by omega, ite_false, Nat.add_zero]
      exact congrArg _ (congrArg _ (by rw [Nat.mul_add, Nat.mul_one]; omega))
    · simp only [t3, ite_false]
      rw [show t + 1 - 4 = 0 by omega, show (vreg (zN l)) = vreg (zN l) from rfl]
      rw [h.z 0 (by decide)]
      obtain rfl : t = 3 := by omega
      simp only [Amm52N.shifted, Lay.L, show ¬ (l.R - 1 + l.R * 3 + 1 < 4 * l.R) by omega, ite_false]
      rfl
  · simp only [nT, hl, ite_false]
    by_cases h0 : kk = 0
    · subst h0
      simp only [ite_true, T.eval]
      rw [a2T_evalS (kk := 0) h hR hp (by omega) ht, cT_eval h hR hp ht]
      have h1 := low_lt h hp (j := 0 + 1 + l.R * t) (idx_lt (by omega) ht)
      have h2 := low_lt h hp (j := 0) (by simp only [Lay.L]; omega)
      have := hi_lt (a p (0 + l.R * t)) (b p)
      have hc : low (ops a m k p) (L p) (b p) 0 / 2 ^ 52 < 2 ^ 11 := Nat.div_lt_of_lt_mul (by omega)
      rw [add_ofNat (by split <;> omega)]
      simp only [Amm52N.shifted, Lay.L, show 0 + l.R * t + 1 = 0 + 1 + l.R * t by omega,
        show 0 + 1 + l.R * t < 4 * l.R by omega, ite_true]
      refine congrArg (BitVec.ofNat 64) ?_
      by_cases t0 : t = 0
      · subst t0; simp only [Nat.mul_zero, ite_true]; omega
      · simp only [t0, ite_false, show 0 + l.R * t ≠ 0 by
          have := Nat.mul_le_mul_left l.R (show 1 ≤ t by omega); omega]
        omega
    · simp only [h0, ite_false]
      obtain ⟨kk', rfl⟩ : ∃ kk', kk = kk' + 1 := ⟨kk - 1, by omega⟩
      rw [a2T_evalS h hR hp (by omega) ht]
      simp only [Amm52N.shifted, Lay.L, show kk' + 1 + l.R * t + 1 < 4 * l.R by omega,
        show kk' + 1 + 1 + l.R * t = kk' + 1 + l.R * t + 1 by omega, show kk' + 1 + l.R * t ≠ 0 by omega,
        ite_true, ite_false, Nat.add_zero]

theorem hT_eval (h : StepIn l s i L a m k b) (hR : 2 ≤ l.R) {p kk t : Nat} (hp : p < 2) (hk : kk < l.R)
    (ht : t < 4) :
    (hT l p kk i).eval s t = BitVec.ofNat 64 (Amm52N.step l.L (ops a m k p) (L p) (b p) (kk + l.R * t)) := by
  have hs : Amm52N.shifted l.L (low (ops a m k p) (L p) (b p)) (kk + l.R * t) < 2 ^ 62 + 2 ^ 54 := by
    unfold Amm52N.shifted
    split
    · have := low_lt h hp (j := kk + l.R * t + 1) (by omega)
      have := low_lt h hp (j := 0) (by simp only [Lay.L]; omega)
      have := Nat.div_le_self (low (ops a m k p) (L p) (b p) 0) (2 ^ 52)
      split
      · have hc : low (ops a m k p) (L p) (b p) 0 / 2 ^ 52 < 2 ^ 11 := Nat.div_lt_of_lt_mul (by omega)
        omega
      · omega
    · omega
  have := hi_lt (a p (kk + l.R * t)) (b p)
  have := hi_lt (m p (kk + l.R * t)) (stepU (ops a m k p) (L p) (b p))
  by_cases hl : kk = l.R - 1
  · simp only [hT, hl, ite_true, T.eval]
    subst hl
    have ha : s.mem.readW (s.gpr .r8 + BitVec.ofNat 64 (l.D * p + 32 * (l.R - 1) + 8 * t)) 64 =
        BitVec.ofNat 64 (a p (l.R - 1 + l.R * t)) := h.ina p hp (l.R - 1) hk t ht
    have hm : s.mem.readW (s.gpr .r10 + BitVec.ofNat 64 (l.D * p + oM + 32 * (l.R - 1) + 8 * t)) 64 =
        BitVec.ofNat 64 (m p (l.R - 1 + l.R * t)) := h.inm p hp (l.R - 1) hk t ht
    rw [nT_eval h hR hp hk ht]
    simp only [↓reduceIte, Nat.add_zero]
    rw [bT_eval h hp, ha, mad_hi (by omega), uT_eval h hR hp, hm, mad_hi (by omega)]
    rfl
  · simp only [hT, hl, ite_false, T.eval]
    rw [nT_eval h hR hp hk ht]
    simp only [hl, ite_false]
    rw [uT_eval h hR hp, h.inm p hp kk hk t ht, mad_hi (by omega)]
    rfl

end

end VG.Proof.Bignum.X86_64.Ifma
