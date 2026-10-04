import VerifiedGarbage.Proof.Bignum.X86_64.AmmTerms
import VerifiedGarbage.Proof.Bignum.Amm52

/-!
# RSA with AVX512_IFMA on x86-64: the lanes of a step

The terms of step `i` (`AmmTerms.lean`) evaluated lane by lane: under
`StepIn` (the lanes of the roles hold the limbs `L p`, below `2⁶¹`; the
operands' limbs, `k₀` and the limb `b p` in memory, below `2⁵²`; register
14 zero), role `k`'s lane `t` after the step holds limb `k + 5 t` of
`Amm52.step` (`hT_eval`).
-/

namespace VG.Proof.Bignum.X86_64.AmmSym

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Impl.Rsa.X86_64.CrtIfma (D oM oK0)
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi qw pick2 sel4)
open VG.Proof.X25519.X86_64.Ifma (mad52 mad52_toNat)

theorem halves (x : BitVec 64) : x.extractLsb' 32 32 ++ x.extractLsb' 0 32 = x := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  rw [BitVec.getLsbD_append]
  by_cases h : j < 32
  · simp [h]
  · simp [h, show j - 32 < 32 by omega, show 32 + (j - 32) = j by omega]

theorem pick2_tt (a b : BitVec 64) : pick2 a b true true = b := by
  simp only [pick2, ite_true, halves]

theorem pick2_ff (a b : BitVec 64) : pick2 a b false false = a := by
  simp only [pick2, Bool.false_eq_true, ite_false, halves]

/-- The machine before step `i`, for limbs `L p`, operand limbs `a p`,
modulus limbs `m p`, `k₀` `k p` and second-operand limb `b p`. -/
structure StepIn (s : State) (i : Nat) (L a m : Nat → Nat → Nat) (k b : Nat → Nat) : Prop where
  z : ∀ t < 4, qw s .xmm14 t = 0
  lanes : ∀ p < 2, ∀ kk < 5, ∀ t < 4, qw s (xr (regOf p kk i)) t = BitVec.ofNat 64 (L p (kk + 5 * t))
  lt : ∀ p < 2, ∀ j < 20, L p j < 2 ^ 61
  ina : ∀ p < 2, ∀ kk < 5, ∀ t < 4,
    s.mem.readW (s.gpr .r8 + BitVec.ofNat 64 (D * p + 32 * kk + 8 * t)) 64 = BitVec.ofNat 64 (a p (kk + 5 * t))
  inm : ∀ p < 2, ∀ kk < 5, ∀ t < 4,
    s.mem.readW (s.gpr .r10 + BitVec.ofNat 64 (D * p + oM + 32 * kk + 8 * t)) 64 =
      BitVec.ofNat 64 (m p (kk + 5 * t))
  ink : ∀ p < 2, ∀ t < 4, s.mem.readW (s.gpr .r10 + BitVec.ofNat 64 (D * p + oK0 + 8 * t)) 64 = BitVec.ofNat 64 (k p)
  inb : ∀ p < 2, s.mem.readW (s.gpr .r9 + BitVec.ofNat 64 (D * p + 32 * i)) 64 = BitVec.ofNat 64 (b p)
  alt : ∀ p < 2, ∀ j < 20, a p j < 2 ^ 52
  mlt : ∀ p < 2, ∀ j < 20, m p j < 2 ^ 52
  klt : ∀ p < 2, k p < 2 ^ 52
  blt : ∀ p < 2, b p < 2 ^ 52

/-- The operands of prime `p`. -/
def ops (a m : Nat → Nat → Nat) (k : Nat → Nat) (p : Nat) : Ops := ⟨a p, m p, k p⟩

theorem lo_comm (x y : Nat) : lo x y = lo y x := by unfold lo; rw [Nat.mul_comm]
theorem hi_comm (x y : Nat) : hi x y = hi y x := by unfold hi; rw [Nat.mul_comm]

theorem ofNat_toNat {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem mad_lo {c x y : Nat} (hc : c + 2 ^ 52 < 2 ^ 64) :
    mad52 false (BitVec.ofNat 64 c) (BitVec.ofNat 64 x) (BitVec.ofNat 64 y) =
      BitVec.ofNat 64 (c + lo y x) := by
  apply BitVec.eq_of_toNat_eq
  have := lo_lt y x
  rw [mad52_toNat]
  simp only [Bool.false_eq_true, ite_false, BitVec.toNat_ofNat]
  have e : ∀ v : Nat, v % 2 ^ 64 % 2 ^ 52 = v % 2 ^ 52 := fun v => Nat.mod_mod_of_dvd _ (by decide)
  rw [e, e, Nat.mul_comm, show y % 2 ^ 52 * (x % 2 ^ 52) % 2 ^ 52 = lo y x from rfl]
  rw [Nat.mod_eq_of_lt (show c % 2 ^ 64 + lo y x < 2 ^ 64 by
    have := Nat.mod_le c (2 ^ 64); omega), Nat.mod_eq_of_lt (show c + lo y x < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega)]

theorem mad_hi {c x y : Nat} (hc : c + 2 ^ 52 < 2 ^ 64) :
    mad52 true (BitVec.ofNat 64 c) (BitVec.ofNat 64 x) (BitVec.ofNat 64 y) =
      BitVec.ofNat 64 (c + hi y x) := by
  apply BitVec.eq_of_toNat_eq
  have := hi_lt y x
  rw [mad52_toNat]
  simp only [ite_true, BitVec.toNat_ofNat]
  have e : ∀ v : Nat, v % 2 ^ 64 % 2 ^ 52 = v % 2 ^ 52 := fun v => Nat.mod_mod_of_dvd _ (by decide)
  rw [e, e, Nat.mul_comm, show y % 2 ^ 52 * (x % 2 ^ 52) / 2 ^ 52 = hi y x from rfl]
  rw [Nat.mod_eq_of_lt (show c % 2 ^ 64 + hi y x < 2 ^ 64 by
    have := Nat.mod_le c (2 ^ 64); omega), Nat.mod_eq_of_lt (show c + hi y x < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega)]

section
variable {s : State} {i : Nat} {L a m : Nat → Nat → Nat} {k b : Nat → Nat}

theorem bT_eval (h : StepIn s i L a m k b) {p : Nat} (hp : p < 2) (t : Nat) :
    (bT p i).eval s t = BitVec.ofNat 64 (b p) := by
  simp only [bT, A.eval, ite_true, G.eval]; exact h.inb p hp

theorem ld_a (h : StepIn s i L a m k b) {p kk t : Nat} (hp : p < 2) (hk : kk < 5) (ht : t < 4) :
    (A.ld .r8 (D * p + 32 * kk)).eval s t = BitVec.ofNat 64 (a p (kk + 5 * t)) := by
  simp only [A.eval]; exact h.ina p hp kk hk t ht

theorem ld_m (h : StepIn s i L a m k b) {p kk t : Nat} (hp : p < 2) (hk : kk < 5) (ht : t < 4) :
    (A.ld .r10 (D * p + oM + 32 * kk)).eval s t = BitVec.ofNat 64 (m p (kk + 5 * t)) := by
  simp only [A.eval]; exact h.inm p hp kk hk t ht

theorem a1T_eval (h : StepIn s i L a m k b) {p kk t : Nat} (hp : p < 2) (hk : kk < 5) (ht : t < 4) :
    (a1T p kk i).eval s t = BitVec.ofNat 64 (L p (kk + 5 * t) + lo (a p (kk + 5 * t)) (b p)) := by
  have hl := h.lt p hp (kk + 5 * t) (by omega)
  simp only [a1T, A.eval]
  rw [h.lanes p hp kk hk t ht, bT_eval h hp, h.ina p hp kk hk t ht, mad_lo (by omega)]

theorem uT_eval (h : StepIn s i L a m k b) {p : Nat} (hp : p < 2) (t : Nat) :
    (uT p i).eval s t = BitVec.ofNat 64 (stepU (ops a m k p) (L p) (b p)) := by
  have hl := h.lt p hp 0 (by decide)
  have := lo_lt (a p 0) (b p)
  simp only [uT, A.eval]
  rw [a1T_eval h hp (by decide) (by decide), show (0 : Nat) + 5 * 0 = 0 from rfl,
    h.ink p hp 0 (by decide),
    show (0 : BitVec 64) = BitVec.ofNat 64 0 from rfl, mad_lo (by omega), Nat.zero_add, lo_comm]
  rfl

theorem a2T_eval (h : StepIn s i L a m k b) {p kk t : Nat} (hp : p < 2) (hk : kk < 5) (ht : t < 4) :
    (a2T p kk i).eval s t = BitVec.ofNat 64 (low (ops a m k p) (L p) (b p) (kk + 5 * t)) := by
  have hl := h.lt p hp (kk + 5 * t) (by omega)
  have := lo_lt (a p (kk + 5 * t)) (b p)
  simp only [a2T, A.eval]
  rw [a1T_eval h hp hk ht, uT_eval h hp, h.inm p hp kk hk t ht, mad_lo (by omega)]
  simp only [low, ops]

theorem low_lt (h : StepIn s i L a m k b) {p j : Nat} (hp : p < 2) (hj : j < 20) :
    low (ops a m k p) (L p) (b p) j < 2 ^ 61 + 2 ^ 53 := by
  have := h.lt p hp j hj
  have := lo_lt (a p j) (b p)
  have := lo_lt (m p j) (stepU (ops a m k p) (L p) (b p))
  show L p j + lo (a p j) (b p) + lo (m p j) (stepU (ops a m k p) (L p) (b p)) < _
  omega

theorem shr_ofNat {x : Nat} (hx : x < 2 ^ 64) : BitVec.ofNat 64 x >>> 52 = BitVec.ofNat 64 (x / 2 ^ 52) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx)]

theorem add_ofNat {x y : Nat} (h : x + y < 2 ^ 64) :
    BitVec.ofNat 64 x + BitVec.ofNat 64 y = BitVec.ofNat 64 (x + y) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show x < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show y < 2 ^ 64 by omega)]

theorem cT_eval (h : StepIn s i L a m k b) {p t : Nat} (hp : p < 2) (ht : t < 4) :
    (cT p i).eval s t =
      BitVec.ofNat 64 (if t = 0 then low (ops a m k p) (L p) (b p) 0 / 2 ^ 52 else 0) := by
  have h0 := low_lt h hp (j := 0) (by decide)
  simp only [cT, A.eval]
  rw [show (VG.Proof.Poly1305.X86_64.Avx2.xr 14) = .xmm14 from rfl, h.z t ht]
  rcases VG.X86_64.cases4 ht with rfl | rfl | rfl | rfl
  · rw [a2T_eval h hp (by decide) (by decide), show (0 : Nat) + 5 * 0 = 0 from rfl, shr_ofNat (by omega),
      show Nat.testBit 3 (2 * 0) = true by decide, show Nat.testBit 3 (2 * 0 + 1) = true by decide, pick2_tt]
    rfl
  · rw [show Nat.testBit 3 (2 * 1) = false by decide, show Nat.testBit 3 (2 * 1 + 1) = false by decide, pick2_ff]
    rfl
  · rw [show Nat.testBit 3 (2 * 2) = false by decide, show Nat.testBit 3 (2 * 2 + 1) = false by decide, pick2_ff]
    rfl
  · rw [show Nat.testBit 3 (2 * 3) = false by decide, show Nat.testBit 3 (2 * 3 + 1) = false by decide, pick2_ff]
    rfl

theorem nT_eval (h : StepIn s i L a m k b) {p kk t : Nat} (hp : p < 2) (hk : kk < 5) (ht : t < 4) :
    (nT p kk i).eval s t = BitVec.ofNat 64 (shifted (low (ops a m k p) (L p) (b p)) (kk + 5 * t)) := by
  unfold nT
  split
  · rename_i h4
    subst h4
    simp only [A.eval]
    rw [show (VG.Proof.Poly1305.X86_64.Avx2.xr 14) = .xmm14 from rfl, h.z t ht]
    rcases VG.X86_64.cases4 ht with rfl | rfl | rfl | rfl
    · rw [show Nat.testBit 192 (2 * 0) = false by decide, show Nat.testBit 192 (2 * 0 + 1) = false by decide,
        pick2_ff, show sel4 57 0 = 1 from rfl, a2T_eval h hp (by decide) (by decide)]; rfl
    · rw [show Nat.testBit 192 (2 * 1) = false by decide, show Nat.testBit 192 (2 * 1 + 1) = false by decide,
        pick2_ff, show sel4 57 1 = 2 from rfl, a2T_eval h hp (by decide) (by decide)]; rfl
    · rw [show Nat.testBit 192 (2 * 2) = false by decide, show Nat.testBit 192 (2 * 2 + 1) = false by decide,
        pick2_ff, show sel4 57 2 = 3 from rfl, a2T_eval h hp (by decide) (by decide)]; rfl
    · rw [show Nat.testBit 192 (2 * 3) = true by decide, show Nat.testBit 192 (2 * 3 + 1) = true by decide,
        pick2_tt]; rfl
  · split
    · rename_i _ h0
      subst h0
      simp only [A.eval]
      rw [a2T_eval h hp (by decide) ht, cT_eval h hp ht]
      have h1 := low_lt h hp (j := 1 + 5 * t) (by omega)
      have h2 := low_lt h hp (j := 0) (by decide)
      have hc : low (ops a m k p) (L p) (b p) 0 / 2 ^ 52 < 2 ^ 10 := Nat.div_lt_of_lt_mul (by omega)
      rw [add_ofNat (by split <;> omega)]
      simp only [shifted, show 0 + 5 * t < 19 by omega, ite_true, show 0 + 5 * t + 1 = 1 + 5 * t by omega]
      congr 2
      rcases VG.X86_64.cases4 ht with rfl | rfl | rfl | rfl <;> simp
    · rename_i h4 h0
      rw [a2T_eval h hp (by omega) ht]
      simp only [shifted, show kk + 5 * t < 19 by omega, ite_true, show kk + 1 + 5 * t = kk + 5 * t + 1 by omega,
        show kk + 5 * t ≠ 0 by omega, ite_false, Nat.add_zero]

theorem hT_eval (h : StepIn s i L a m k b) {p kk t : Nat} (hp : p < 2) (hk : kk < 5) (ht : t < 4) :
    (hT p kk i).eval s t = BitVec.ofNat 64 (step (ops a m k p) (L p) (b p) (kk + 5 * t)) := by
  have hs : shifted (low (ops a m k p) (L p) (b p)) (kk + 5 * t) < 2 ^ 61 + 2 ^ 54 := by
    unfold shifted
    split
    · have := low_lt h hp (j := kk + 5 * t + 1) (by omega)
      have := low_lt h hp (j := 0) (by decide)
      have := Nat.div_le_self (low (ops a m k p) (L p) (b p) 0) (2 ^ 52)
      split <;> omega
    · omega
  have := hi_lt (a p (kk + 5 * t)) (b p)
  simp only [hT, A.eval]
  rw [nT_eval h hp hk ht, bT_eval h hp, h.ina p hp kk hk t ht, mad_hi (by omega), uT_eval h hp,
    h.inm p hp kk hk t ht, mad_hi (by omega)]
  rfl

end

end VG.Proof.Bignum.X86_64.AmmSym
