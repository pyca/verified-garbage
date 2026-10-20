module

public import VerifiedGarbage.Proof.Ffdh.KeyScalar
import VerifiedGarbage.Proof.Bignum.Octets

/-! Scalar sampling at an arbitrary public maximum bit length, including zero. -/

@[expose] public section
namespace VG.Proof.Ffdh.ScalarWidth
open VG
open VG.Spec.Rsa (os2ip)

/-- Retain one byte even at zero bits, with a zero mask on that byte. -/
def width (bits : Nat) : Nat := max 1 ((bits + 7) / 8)

def headBits (bits : Nat) : Nat := bits - 8 * (width bits - 1)

def mask (bits : Nat) : Byte := BitVec.ofNat 8 (2 ^ headBits bits - 1)

theorem width_pos (bits : Nat) : 0 < width bits := by unfold width; omega

theorem headBits_parts (bits : Nat) :
    headBits bits ≤ 8 ∧ 8 * (width bits - 1) + headBits bits = bits := by
  unfold headBits width
  omega

theorem width_le {bits k : Nat} (positive : 0 < k) (fits : bits ≤ 8 * k) :
    width bits ≤ k := by unfold width; omega

theorem mask_toNat (bits : Nat) : (mask bits).toNat = 2 ^ headBits bits - 1 := by
  have limit : 2 ^ headBits bits ≤ 256 :=
    Nat.pow_le_pow_right (by decide) (headBits_parts bits).1
  have nonzero := Nat.one_le_two_pow (n := headBits bits)
  change (2 ^ headBits bits - 1) % 256 = _
  exact Nat.mod_eq_of_lt (by omega)

/-- Public-width masking cuts the uniform entropy draw modulo precisely `2^bits`. -/
theorem cut_value {r : List Byte} {bits : Nat} (nonempty : 0 < r.length)
    (fits : bits ≤ 8 * r.length) :
    os2ip (KeyScalar.cut r (r.length - width bits) (mask bits)) =
      os2ip r % 2 ^ bits := by
  have size := width_le nonempty fits
  have parts := headBits_parts bits
  have value := KeyScalar.cut_value
    (n := r.length - width bits) (e := width bits) (j := headBits bits)
    (by omega : r.length = r.length - width bits + width bits)
    (by have := width_pos bits; omega) parts.1 (mask_toNat bits)
  rw [parts.2] at value
  exact value

theorem cut_length {r : List Byte} {bits : Nat} (nonempty : 0 < r.length)
    (fits : bits ≤ 8 * r.length) :
    (KeyScalar.cut r (r.length - width bits) (mask bits)).length = r.length := by
  apply KeyScalar.cut_length
  have := width_le nonempty fits
  have := width_pos bits
  omega

end VG.Proof.Ffdh.ScalarWidth
