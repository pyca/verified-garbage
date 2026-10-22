module

public import VerifiedGarbage.Proof.MillerRabin.X86.LowBits
import VerifiedGarbage.Proof.Rc2.PairMem

/-! # The prepared one-hot tail computes exactly the shared final threshold -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Spec.Rsa.Mont (arrAt)

theorem tail_fold {m : Mem} {base : Addr} {w t : Nat} (ht : t < 64)
    (tail : m.readW (off base (arrAt w 27 + 8 * w)) 64 = BitVec.twoPow 64 t) :
    VG.Proof.MillerRabin.Math.foldR (m.readW (off base (arrAt w 27 + 8 * w)) 32)
      (m.readW (off base (arrAt w 27 + 8 * w + 4)) 32) =
      BitVec.ofNat 32 (4 - VG.Proof.RsaKeyGen.sigOf t) := by
  have pair := congrArg BitVec.toNat (VG.Proof.Rc2.Word32.read64_pair m (off base (arrAt w 27 + 8 * w)))
  have highAddr : off base (arrAt w 27 + 8 * w) + BitVec.ofNat 64 4 =
      off base (arrAt w 27 + 8 * w + 4) := by
    unfold off
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have bound : 2 ^ t < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) ht
  rw [tail, BitVec.toNat_twoPow, Nat.mod_eq_of_lt bound, BitVec.toNat_append, highAddr] at pair
  rw [← Nat.shiftLeft_add_eq_or_of_lt (m.readW (off base (arrAt w 27 + 8 * w)) 32).isLt,
    Nat.shiftLeft_eq] at pair
  have loBound := (m.readW (off base (arrAt w 27 + 8 * w)) 32).isLt
  have hiBound := (m.readW (off base (arrAt w 27 + 8 * w + 4)) 32).isLt
  have lo : m.readW (off base (arrAt w 27 + 8 * w)) 32 = BitVec.ofNat 32 (2 ^ t % 2 ^ 32) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_mod]
    omega
  have hi : m.readW (off base (arrAt w 27 + 8 * w + 4)) 32 = BitVec.ofNat 32 (2 ^ t / 2 ^ 32) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    omega
  rw [lo, hi]
  exact VG.Proof.MillerRabin.Math.foldR_eq t ht

end VG.Proof.MillerRabin.X86
