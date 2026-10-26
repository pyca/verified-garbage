module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Controller
import VerifiedGarbage.Proof.Rc2.PairMem
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Util.CompileInductive

/-! Preserve the complete u64 attempt budget, including the initial 2^32 value. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Mont
open VG.Proof.Ffdh.Arm.KeySearch (lowWord)

theorem packedLow (m : Mem) (base : BitVec 32) (j n : Nat) (bound : n < 2 ^ 64)
    (value : m.readW (off (State.addr base) (8 * j)) 64 = BitVec.ofNat 64 n) :
    lowWord m base j = BitVec.ofNat 32 n := by
  unfold lowWord
  rw [← VG.Proof.Rc2.Word32.readW64_lo, value]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero, Nat.mod_eq_of_lt bound]

theorem packedHigh (m : Mem) (base : BitVec 32) (j n : Nat) (bound : n < 2 ^ 64)
    (value : m.readW (off (State.addr base) (8 * j)) 64 = BitVec.ofNat 64 n) :
    m.readW (off (State.addr base) (8 * j + 4)) 32 = BitVec.ofNat 32 (n / 2 ^ 32) := by
  have address : off (State.addr base) (8 * j + 4) = off (State.addr base) (8 * j) + BitVec.ofNat 64 4 := by
    simp only [off, BitVec.ofNat_add, BitVec.add_assoc]
  rw [address, ← VG.Proof.Rc2.Word32.readW64_hi, value]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt bound]

theorem pairOfNat (n : Nat) (bound : n < 2 ^ 64) :
    ((BitVec.ofNat 32 (n / 2 ^ 32)) ++ (BitVec.ofNat 32 n) : BitVec 64) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (BitVec.ofNat 32 n).isLt]
  have high : n / 2 ^ 32 < 2 ^ 32 := by omega
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt high, Nat.mod_eq_of_lt bound, Nat.shiftLeft_eq]
  have split := Nat.mod_add_div n (2 ^ 32)
  omega

theorem packedCounter (m : Mem) (base : BitVec 32) (j n : Nat) (bound : n < 2 ^ 64)
    (low : lowWord m base j = BitVec.ofNat 32 n)
    (high : m.readW (off (State.addr base) (8 * j + 4)) 32 = BitVec.ofNat 32 (n / 2 ^ 32)) :
    m.readW (off (State.addr base) (8 * j)) 64 = BitVec.ofNat 64 n := by
  rw [VG.Proof.Rc2.Word32.read64_pair]
  have address : off (State.addr base) (8 * j) + BitVec.ofNat 64 4 = off (State.addr base) (8 * j + 4) := by
    simp only [off, BitVec.ofNat_add, BitVec.add_assoc]
  rw [address, high, show m.readW (off (State.addr base) (8 * j)) 32 = BitVec.ofNat 32 n from low]
  exact pairOfNat n bound

theorem writeCounter (m : Mem) (base : BitVec 32) (n : Nat) (bound : n < 2 ^ 64) :
    (m.writeW (State.addr base) (BitVec.ofNat 32 n)).writeW (off (State.addr base) 4)
      (BitVec.ofNat 32 (n / 2 ^ 32)) = m.writeW (State.addr base) (BitVec.ofNat 64 n) := by
  rw [← pairOfNat n bound, VG.Proof.Rc2.Word32.write64_pair]

end VG.Proof.Ffdh.Arm.ParameterSearch
