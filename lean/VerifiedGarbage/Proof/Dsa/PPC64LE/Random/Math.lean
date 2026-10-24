module

public import VerifiedGarbage.Spec.Dsa.Random
import VerifiedGarbage.Proof.Dsa.DomainShape
import VerifiedGarbage.Proof.Dsa.RandomRange
import VerifiedGarbage.Proof.Dsa.RandomEncoding
import VerifiedGarbage.Proof.Dsa.RandomBytes
import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Spec.RsaPss
public import VerifiedGarbage.TCB.Mem

/-!
# DSA sampling on PPC64LE: the arithmetic of the registers

What the sampler's instructions compute, on 64-bit registers: the mask of
q's first significant octet (`smear_eq`, its bits smeared right), a masked
octet (`mask_byte`), the test of a short tape (`short_eq`), a step of the
borrow chain (`borrow_eq`), and the test of `q > 1` (`valid_eq`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Rnd

open VG

/-- The mask of the significant bits of a nonzero octet `n`. -/
abbrev maskOf (n : Nat) : Nat := 2 ^ (n.log2 + 1) - 1

/-- `x` with its bits smeared right, as the code computes it. -/
def smear (x : BitVec 64) : BitVec 64 :=
  ((x ||| x >>> 1) ||| (x ||| x >>> 1) >>> 2) ||| ((x ||| x >>> 1) ||| (x ||| x >>> 1) >>> 2) >>> 4

/-- The same on numbers. -/
def smearN (n : Nat) : Nat :=
  ((n ||| n >>> 1) ||| (n ||| n >>> 1) >>> 2) ||| ((n ||| n >>> 1) ||| (n ||| n >>> 1) >>> 2) >>> 4

theorem or_lt {a b : Nat} (ha : a < 256) (hb : b < 256) : a ||| b < 256 :=
  Nat.or_lt_two_pow (n := 8) ha hb

theorem shr_lt {a k : Nat} (ha : a < 256) : a >>> k < 256 := by
  rw [Nat.shiftRight_eq_div_pow]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha

theorem ofNat_or {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ofNat 64 a ||| BitVec.ofNat 64 b = BitVec.ofNat 64 (a ||| b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt (Nat.or_lt_two_pow ha hb)]

theorem ofNat_shr {a : Nat} (ha : a < 2 ^ 64) (k : Nat) :
    BitVec.ofNat 64 a >>> k = BitVec.ofNat 64 (a >>> k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt (by rw [Nat.shiftRight_eq_div_pow]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha)]

theorem smear_ofNat {n : Nat} (hn : n < 256) : smear (BitVec.ofNat 64 n) = BitVec.ofNat 64 (smearN n) := by
  have h1 : n ||| n >>> 1 < 256 := or_lt hn (shr_lt hn)
  have h2 : (n ||| n >>> 1) ||| (n ||| n >>> 1) >>> 2 < 256 := or_lt h1 (shr_lt h1)
  unfold smear smearN
  rw [ofNat_shr (by omega), ofNat_or (by omega) (by have := shr_lt (k := 1) hn; omega),
    ofNat_shr (by omega), ofNat_or (by omega) (by have := shr_lt (k := 2) h1; omega),
    ofNat_shr (by omega), ofNat_or (by omega) (by have := shr_lt (k := 4) h2; omega)]

theorem smearN_eq : ∀ n < 256, 0 < n → smearN n = maskOf n := by decide +kernel

/-- The mask of a nonzero octet. -/
theorem smear_eq {n : Nat} (hn : n < 256) (h0 : 0 < n) :
    smear (BitVec.ofNat 64 n) = BitVec.ofNat 64 (maskOf n) := by
  rw [smear_ofNat hn, smearN_eq n hn h0]

theorem maskOf_lt {n : Nat} (hn : n < 256) (h0 : 0 < n) : maskOf n < 256 := by
  have := (Nat.log2_lt (show n ≠ 0 by omega)).mpr (show n < 2 ^ 8 by omega)
  have : 2 ^ (n.log2 + 1) ≤ 2 ^ 8 := Nat.pow_le_pow_right (by decide) (by omega)
  have := Nat.two_pow_pos (n.log2 + 1)
  simp only [maskOf]; omega

/-- An octet masked in a register, stored as an octet. -/
theorem mask_byte (b : Byte) {M : Nat} (hM : M < 256) :
    (BitVec.ofNat 64 b.toNat &&& BitVec.ofNat 64 M).setWidth 8 = b &&& BitVec.ofNat 8 M := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := b.toNat) (by have := b.isLt; omega),
    Nat.mod_eq_of_lt (a := M) (by omega), Nat.mod_eq_of_lt (a := M) (by omega),
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left (by have := b.isLt; omega))]

/-- An octet with all ones, stored as an octet. -/
theorem mask_byte_ff (b : Byte) : (BitVec.ofNat 64 b.toNat &&& BitVec.ofNat 64 255).setWidth 8 = b := by
  rw [mask_byte b (by decide)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat]
  exact Nat.and_two_pow_sub_one_of_lt_two_pow (n := 8) b.isLt

/-- The test of a short tape: 1 exactly when fewer than `w` octets are left. -/
theorem short_eq {x w : Nat} (hx : x < 2 ^ 64) (hw : w ≤ 32) :
    ((BitVec.ofNat 64 x >>> 63) ^^^ BitVec.ofNat 64 1) &&& ((BitVec.ofNat 64 x - BitVec.ofNat 64 w) >>> 63) =
      BitVec.ofNat 64 (if x < w then 1 else 0) := by
  have ha : BitVec.ofNat 64 x >>> 63 = BitVec.ofNat 64 (if x < 2 ^ 63 then 0 else 1) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.shiftRight_eq_div_pow]
    split
    · rw [Nat.div_eq_of_lt (by omega)]; rfl
    · rw [show x / 2 ^ 63 = 1 by omega]; rfl
  have hb : (BitVec.ofNat 64 x - BitVec.ofNat 64 w) >>> 63 =
      BitVec.ofNat 64 (if x < w then 1 else if x < 2 ^ 63 then 0 else if x - w < 2 ^ 63 then 0 else 1) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt (a := w) (by omega), Nat.shiftRight_eq_div_pow]
    split
    · rw [show (2 ^ 64 - w + x) % 2 ^ 64 = 2 ^ 64 - w + x by omega,
        show (2 ^ 64 - w + x) / 2 ^ 63 = 1 by omega]; rfl
    · rw [show (2 ^ 64 - w + x) % 2 ^ 64 = x - w by omega]
      split
      · rw [Nat.div_eq_of_lt (by omega)]; rfl
      · split
        · rw [Nat.div_eq_of_lt (by omega)]; rfl
        · rw [show (x - w) / 2 ^ 63 = 1 by omega]; rfl
  rw [ha, hb]
  by_cases h1 : x < w
  · rw [ite_eq_left (show x < 2 ^ 63 by omega), ite_eq_left h1, ite_eq_left h1]; rfl
  · rw [ite_eq_right h1, ite_eq_right h1]
    by_cases h2 : x < 2 ^ 63
    · rw [ite_eq_left h2, ite_eq_left h2]; rfl
    · rw [ite_eq_right h2, ite_eq_right h2]; split <;> rfl

/-- A step of the borrow chain: the borrow out of `k − (q + b)`. -/
theorem borrow_eq {k q b : Nat} (hk : k < 256) (hq : q < 256) (hb : b ≤ 1) :
    (BitVec.ofNat 64 k - (BitVec.ofNat 64 q + BitVec.ofNat 64 b)) >>> 63 =
      BitVec.ofNat 64 (if k < q + b then 1 else 0) := by
  rw [← BitVec.ofNat_add]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt (a := q + b) (by omega), Nat.shiftRight_eq_div_pow]
  split
  · rw [show (2 ^ 64 - (q + b) + k) % 2 ^ 64 = 2 ^ 64 - (q + b) + k by omega,
      show (2 ^ 64 - (q + b) + k) / 2 ^ 63 = 1 by omega]
    rfl
  · rw [show (2 ^ 64 - (q + b) + k) % 2 ^ 64 = k - (q + b) by omega, Nat.div_eq_of_lt (by omega)]
    rfl

/-- `(0 − x) >> 63` for `x < 2⁶³`: whether `x` is not zero. -/
theorem nz_eq {x : Nat} (hx : x < 2 ^ 63) :
    (BitVec.ofNat 64 0 - BitVec.ofNat 64 x) >>> 63 = BitVec.ofNat 64 (if x = 0 then 0 else 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := x) (by omega), Nat.shiftRight_eq_div_pow]
  split
  · subst x; rfl
  · rw [show (2 ^ 64 - x + 0 % 2 ^ 64) % 2 ^ 64 = 2 ^ 64 - x by omega,
      show (2 ^ 64 - x) / 2 ^ 63 = 1 by omega]
    rfl

/-- The test of `q > 1` from its significant octets `w` and the first `t`:
`w ≠ 0`, and `w ≥ 2` or `t ≥ 2`. -/
theorem valid_eq {w t : Nat} (hw : w < 256) (ht : t < 256) :
    BitVec.ofNat 64 (if (w >>> 1 ||| t >>> 1) = 0 then 0 else 1) &&&
        BitVec.ofNat 64 (if w = 0 then 0 else 1) =
      BitVec.ofNat 64 (if w ≠ 0 ∧ (2 ≤ w ∨ 2 ≤ t) then 1 else 0) := by
  have e : (w >>> 1 ||| t >>> 1) = 0 ↔ w < 2 ∧ t < 2 := by
    rw [Nat.or_eq_zero_iff, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]; omega
  generalize (w >>> 1 ||| t >>> 1) = z at e ⊢
  have e1 := e.mp
  have e2 := e.mpr
  split <;> split <;> split <;> first | rfl | (exfalso; omega)

end VG.Proof.Dsa.PPC64LE.Rnd
