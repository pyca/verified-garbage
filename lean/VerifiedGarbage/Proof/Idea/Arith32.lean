import VerifiedGarbage.Proof.Idea.Arith

/-!
# IDEA: word arithmetic on 32-bit registers

As `Proof/Idea/Arith.lean`, for targets with 32-bit registers, whose
multiplication keeps only the low 32 bits of a product of residues (up to
2³²): ⊙'s operands' residues (`prep32_toNat`), and its reduction from the
halves of the product less one (`reduce32`), which no wrap-around changes;
⊞, XOR and the bytes of words on zero-extended words.
-/

namespace VG.Proof.Idea

open VG

theorem mask32_toNat (x m : BitVec 32) (hm : m.toNat = 65535) :
    (x &&& m).toNat = x.toNat % 65536 := by
  rw [BitVec.toNat_and, hm, show 65535 = 2 ^ 16 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

/-- `((x - 1) & 0xffff) + 1` is the residue of `x`'s low word. -/
theorem prep32_toNat (a m : BitVec 32) (hm : m.toNat = 65535) :
    (((a - 1) &&& m) + 1 : BitVec 32).toNat = Spec.Idea.residue (a.setWidth 16) := by
  have h1 : (1 : BitVec 32).toNat = 1 := rfl
  rw [BitVec.toNat_add, mask32_toNat _ _ hm, BitVec.toNat_sub, h1]
  unfold Spec.Idea.residue
  have hs : (a.setWidth 16).toNat = a.toNat % 65536 := by simp [BitVec.toNat_setWidth]
  split
  · rename_i h
    have h' : a.toNat % 65536 = 0 := by rw [← hs, h]; rfl
    omega
  · rename_i h
    have h' : a.toNat % 65536 ≠ 0 := by
      intro h''; apply h; apply BitVec.eq_of_toNat_eq; rw [hs, h'']; rfl
    rw [hs]; omega

theorem reduce_nat (H L : Nat) (hL : L < 65536) (hH : H < 65536) :
    ((L + 1 + (2 ^ 32 - H)) % 2 ^ 32 + (L + 1 + (2 ^ 32 - H)) % 2 ^ 32 / 2 ^ 31) % 2 ^ 32 % 65536 =
      (65536 * H + L + 1) % 65537 % 65536 := by
  have e₁ : 65536 * H + L + 1 = (L + 1 + 65537 - H) + 65537 * (H - 1) ∨ H = 0 := by omega
  by_cases hc : H ≤ L + 1
  · have e : (L + 1 + (2 ^ 32 - H)) % 2 ^ 32 = L + 1 - H := by omega
    have e2 : 65536 * H + L + 1 = (L + 1 - H) + 65537 * H := by omega
    have r1 : (65536 * H + L + 1) % 65537 = L + 1 - H := by
      rw [e2, Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt (by omega)
    rw [e, r1]; omega
  · have e : (L + 1 + (2 ^ 32 - H)) % 2 ^ 32 = 2 ^ 32 - (H - L - 1) := by omega
    have e2 : 65536 * H + L + 1 = (65538 - (H - L)) + 65537 * (H - 1) := by omega
    have r1 : (65536 * H + L + 1) % 65537 = 65538 - (H - L) := by
      rw [e2, Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt (by omega)
    rw [e, r1]; omega

/-- The product `p` (`1 ≤ p ≤ 2³²`) modulo 2¹⁶ + 1, as the code computes it
from `q = p - 1`, which a 32-bit register holds exactly. -/
theorem reduce32 (p : Nat) (hp₀ : 1 ≤ p) (hp : p ≤ 2 ^ 32) (q m one : BitVec 32)
    (hq : q.toNat = p - 1) (hm : m.toNat = 65535) (h1 : one.toNat = 1) :
    (((q &&& m) + one - q >>> 16) + ((q &&& m) + one - q >>> 16) >>> 31) &&& m =
      BitVec.ofNat 32 (p % 65537 % 65536) := by
  generalize hH : (p - 1) / 65536 = H
  generalize hL : (p - 1) % 65536 = L
  have hdec : p = 65536 * H + L + 1 := by omega
  have hL' : L < 65536 := by omega
  have hH' : H < 65536 := by omega
  have hlo : (q &&& m).toNat = L := by rw [mask32_toNat _ _ hm, hq, hL]
  have hhi : (q >>> 16).toNat = H := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hq, ← hH]
  generalize hr' : (q &&& m) + one - q >>> 16 = r
  have hr : r.toNat = (L + 1 + (2 ^ 32 - H)) % 2 ^ 32 := by
    rw [← hr', BitVec.toNat_sub, BitVec.toNat_add, hlo, hhi, h1]
    omega
  apply BitVec.eq_of_toNat_eq
  rw [mask32_toNat _ _ hm, BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hr,
    BitVec.toNat_ofNat, hdec]
  rw [Nat.mod_eq_of_lt (a := _ % 65536) (by omega)]
  exact reduce_nat H L hL' hH'

theorem mul32_toNat (a b : Spec.Idea.Word) :
    (Spec.Idea.mul a b).setWidth 32 =
      BitVec.ofNat 32 (Spec.Idea.residue a * Spec.Idea.residue b % 65537 % 65536) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Spec.Idea.mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat]

theorem setWidth_setWidth16_32 (x : BitVec 16) : (x.setWidth 32).setWidth 16 = x := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

theorem mask32_setWidth (x : BitVec 32) : x &&& 65535 = (x.setWidth 16).setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  rw [mask32_toNat _ _ rfl]
  simp only [BitVec.toNat_setWidth]
  omega

/-- `add r, y; and r, 0xffff` on a zero-extended word. -/
theorem add_mask32 (x : BitVec 16) (y : BitVec 32) :
    (x.setWidth 32 + y) &&& 65535 = (x + y.setWidth 16).setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  rw [mask32_toNat _ _ rfl]
  simp only [BitVec.toNat_add, BitVec.toNat_setWidth]
  omega

theorem add_setWidth32 (x y : BitVec 16) :
    (x.setWidth 32 + y.setWidth 32).setWidth 16 = x + y := by
  rw [BitVec.setWidth_add _ _ (by decide), setWidth_setWidth16_32, setWidth_setWidth16_32]

theorem xor_setWidth32 (x y : BitVec 16) :
    x.setWidth 32 ^^^ y.setWidth 32 = (x ^^^ y).setWidth 32 := by
  rw [BitVec.setWidth_xor]

theorem neg_mask32 (x : BitVec 32) : (0 - x) &&& 65535 = (-(x.setWidth 16)).setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  rw [mask32_toNat _ _ rfl]
  simp only [BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_neg,
    show (0 : BitVec 32).toNat = 0 from rfl]
  omega

/-- Two bytes, big-endian, as the code assembles them. -/
theorem bytes16_32 (x y : BitVec 8) :
    (y.setWidth 32 ||| x.setWidth 32 <<< 8) = (x ++ y).setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_append,
    Nat.shiftLeft_eq]
  have hx := x.isLt
  have hy := y.isLt
  rw [Nat.mod_eq_of_lt (by omega : x.toNat < 2 ^ 32), Nat.mod_eq_of_lt (by omega : y.toNat < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : x.toNat * 2 ^ 8 < 2 ^ 32), Nat.or_comm]
  exact (Nat.mod_eq_of_lt (Nat.or_lt_two_pow (by omega) (by omega))).symm

theorem lo8_32 (x : BitVec 16) : (x.setWidth 32).setWidth 8 = x.setWidth 8 :=
  BitVec.setWidth_setWidth_of_le _ (by decide)

theorem hi8_32 (x : BitVec 16) : ((x.setWidth 32) >>> 8).setWidth 8 = (x >>> 8).setWidth 8 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  rw [Nat.mod_eq_of_lt (by omega : x.toNat < 2 ^ 32)]

end VG.Proof.Idea
