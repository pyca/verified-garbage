module

public import VerifiedGarbage.TCB.Mem
public import VerifiedGarbage.Spec.Rsa
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# RSAES-OAEP encryption on PPC64LE: arithmetic

Untrusted: everything here is checked by Lean. A comparison of values below
`2⁶³` as the top bit of their difference (`ltBit`, `msgBit`), the selection of
`min(a, b)` from it (`minSel`), the bytes of the counter (`trunc8`, `shr8`,
`i2osp_four`) and of an exclusive-or (`byte_xor`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE

open VG

theorem ltBit {x y : Nat} (hx : x < 2 ^ 63) (hy : y < 2 ^ 63) :
    (BitVec.ofNat 64 x - BitVec.ofNat 64 y) >>> 63 = if x < y then 1 else 0 := by
  have e : ((BitVec.ofNat 64 x - BitVec.ofNat 64 y) >>> 63).toNat = if x < y then 1 else 0 := by
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    split <;> omega
  apply BitVec.eq_of_toNat_eq; rw [e]; split <;> rfl

theorem ne_zero_ltBit {x y : Nat} (hx : x < 2 ^ 63) (hy : y < 2 ^ 63) :
    ((BitVec.ofNat 64 x - BitVec.ofNat 64 y) >>> 63 != 0) = decide (x < y) := by
  rw [ltBit hx hy]; split <;> simp_all

/-- The test of `chkMsg`: the top bit of `y`, or of `x - y`, for `x < 2⁶³`. -/
theorem msgBit {x y : Nat} (hx : x < 2 ^ 63) (hy : y < 2 ^ 64) :
    ((BitVec.ofNat 64 y >>> 63 ||| (BitVec.ofNat 64 x - BitVec.ofNat 64 y) >>> 63) != 0) = decide (x < y) := by
  by_cases h : y < 2 ^ 63
  · rw [ltBit hx h]
    have e : BitVec.ofNat 64 y >>> 63 = 0 := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
      rw [Nat.mod_eq_of_lt (by omega)]; simp; omega
    rw [e]; split <;> rename_i hxy <;> simp only [hxy, decide_true, decide_false] <;> decide
  · have e : BitVec.ofNat 64 y >>> 63 = 1 := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
      rw [Nat.mod_eq_of_lt hy]; simp; omega
    rw [e, decide_eq_true (by omega), bne_iff_ne]
    intro h0
    have := congrArg (fun v : BitVec 64 => v.getLsbD 0) h0
    simp at this

/-- `b + ((a - b) ∧ -(a < b))`: `min(a, b)`. -/
theorem minSel {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    BitVec.ofNat 64 b + ((BitVec.ofNat 64 a - BitVec.ofNat 64 b) &&&
      (BitVec.ofNat 64 0 - (BitVec.ofNat 64 a - BitVec.ofNat 64 b) >>> 63)) = BitVec.ofNat 64 (min b a) := by
  rw [ltBit ha hb]
  by_cases h : a < b
  · rw [ite_eq_left h, show BitVec.ofNat 64 0 - 1 = BitVec.allOnes 64 by decide, BitVec.and_allOnes,
      Nat.min_eq_right (by omega)]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  · rw [ite_eq_right h, show BitVec.ofNat 64 0 - 0 = 0#64 by decide, BitVec.and_zero, BitVec.add_zero,
      Nat.min_eq_left (by omega)]

theorem trunc8 (x : Nat) : BitVec.setWidth 8 (BitVec.ofNat 64 x) = BitVec.ofNat 8 x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_mod_of_dvd _ (by decide)]

theorem shr8 {x : Nat} (hx : x < 2 ^ 64) : BitVec.ofNat 64 x >>> 8 = BitVec.ofNat 64 (x / 2 ^ 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx)]

/-- `I2OSP(c, 4)`, byte by byte. -/
theorem i2osp_four (c : Nat) :
    Spec.Rsa.i2osp c 4 = [BitVec.ofNat 8 (c / 2 ^ 8 / 2 ^ 8 / 2 ^ 8), BitVec.ofNat 8 (c / 2 ^ 8 / 2 ^ 8),
      BitVec.ofNat 8 (c / 2 ^ 8), BitVec.ofNat 8 c] := by
  simp only [Spec.Rsa.i2osp, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
    List.map_nil, List.cons_append, Nat.div_div_eq_div_mul, Nat.reducePow, Nat.reduceMul, Nat.reduceSub,
    Nat.pow_zero, Nat.div_one]

theorem byte64 (b : Byte) : ((b.setWidth 64)).setWidth 8 = b := by
  apply BitVec.eq_of_toNat_eq; simp

theorem byte_xor (x y : Byte) : BitVec.setWidth 8 (x.setWidth 64 ^^^ y.setWidth 64) = x ^^^ y := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_xor]
  have := x.isLt
  have := y.isLt
  rw [Nat.mod_eq_of_lt (a := x.toNat) (by omega), Nat.mod_eq_of_lt (a := y.toNat) (by omega)]
  have : x.toNat ^^^ y.toNat < 2 ^ 8 := Nat.xor_lt_two_pow (by omega) (by omega)
  omega

end VG.Proof.RsaOaep.PPC64LE
