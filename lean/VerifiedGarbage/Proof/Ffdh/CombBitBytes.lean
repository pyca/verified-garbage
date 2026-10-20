module

public import VerifiedGarbage.Spec.Rsa
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.PlainSimp
import Init.Data.Nat.Bitwise.Lemmas

/-! A public big-endian byte index exposes exactly one exponent bit. -/

@[expose] public section
namespace VG.Proof.Ffdh.CombBitBytes
open VG VG.Spec.Rsa

theorem byte_value (bs : List Byte) (i : Nat) (hi : i < bs.length) :
    bs[i].toNat = os2ip bs / 256 ^ (bs.length - 1 - i) % 256 := by
  have h := congrArg (fun xs : List Byte => xs[i]?) (VG.Proof.Rsa.i2osp_os2ip bs)
  have e : BitVec.ofNat 8 (os2ip bs / 256 ^ (bs.length - 1 - i)) = bs[i] := by
    simpa [i2osp, hi] using h
  have v := congrArg BitVec.toNat e
  simpa only [BitVec.toNat_ofNat] using v.symm

theorem os2ip_bit (bs : List Byte) (k : Nat) (hk : k < 8 * bs.length) :
    os2ip bs / 2 ^ k % 2 =
      bs[bs.length - 1 - k / 8].toNat / 2 ^ (k % 8) % 2 := by
  have hj : bs.length - 1 - k / 8 < bs.length := by omega
  have byte := byte_value bs (bs.length - 1 - k / 8) hj
  have index : bs.length - 1 - (bs.length - 1 - k / 8) = k / 8 := by omega
  have power : 256 ^ (k / 8) = 2 ^ (8 * (k / 8)) := by
    rw [Nat.pow_mul]
  have bits : Nat.testBit bs[bs.length - 1 - k / 8].toNat (k % 8) = Nat.testBit (os2ip bs) k := by
    rw [byte, index, power, show (256 : Nat) = 2 ^ 8 from rfl, Nat.testBit_mod_two_pow,
      decide_eq_true (Nat.mod_lt k (by decide : 0 < 8)), Bool.true_and,
      ← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight]
    congr 1
    omega
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq] at bits
  have a : os2ip bs / 2 ^ k % 2 < 2 := Nat.mod_lt _ (by decide)
  have b : bs[bs.length - 1 - k / 8].toNat / 2 ^ (k % 8) % 2 < 2 := Nat.mod_lt _ (by decide)
  by_cases ha : os2ip bs / 2 ^ k % 2 = 1
  · have hb : bs[bs.length - 1 - k / 8].toNat / 2 ^ (k % 8) % 2 = 1 := by
      simpa [ha] using bits
    omega
  · have hb : bs[bs.length - 1 - k / 8].toNat / 2 ^ (k % 8) % 2 ≠ 1 := by
      intro h
      simp [h, ha] at bits
    omega

end VG.Proof.Ffdh.CombBitBytes
