module

public import VerifiedGarbage.Proof.Rsa.MontContract
import VerifiedGarbage.Proof.Bignum.ReadPrefix
import VerifiedGarbage.Proof.Bignum.ModulusCheckMath
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # The first packed byte determines a precomputed modulus's parity -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG
open VG.Proof.Rsa.Mont (numAt arrAt)

theorem numAt_byte_parity (m : Mem) (base : Addr) {w o : Nat} (positive : 0 < w) :
    (m (base + BitVec.ofNat 64 (arrAt w o))).toNat % 2 = numAt m base w o % 2 := by
  have low := congrArg BitVec.toNat (read_prefix m (base + BitVec.ofNat 64 (arrAt w o))
    (n := 8 * w) (k := 1) (by omega))
  simp only [BitVec.toNat_setWidth] at low
  have first (a : Addr) : (m.read a 1).toNat = (m a).toNat := by
    change (0#0 ++ m a : BitVec 8).toNat = (m a).toNat
    rw [BitVec.toNat_append]
    simp
  rw [first] at low
  unfold numAt
  omega

theorem numAt_parity_word (m : Mem) (base : Addr) {w o : Nat} (positive : 0 < w) :
    (m (base + BitVec.ofNat 64 (arrAt w o))).setWidth 32 &&& 1 =
      BitVec.ofNat 32 (numAt m base w o % 2) := by
  have byteFit : (m (base + BitVec.ofNat 64 (arrAt w o))).toNat < 2 ^ 32 := by
    have := (m (base + BitVec.ofNat 64 (arrAt w o))).isLt
    omega
  rw [parity_word, BitVec.toNat_setWidth, Nat.mod_eq_of_lt byteFit,
    numAt_byte_parity m base (o := o) positive]

end VG.Proof.Bignum.Arm
