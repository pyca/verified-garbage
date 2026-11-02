module

public import VerifiedGarbage.Proof.MillerRabin.X86.EntryValues
public import VerifiedGarbage.Proof.RsaKeyGen.MrWindow
import VerifiedGarbage.Proof.Rc2.PairMem

/-! # Split the prepared exponent marker into the two native i686 words -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.RsaKeyGen

theorem marker_halves {m : Mem} {W : Addr} {d k : Nat} (bound : k < 64)
    (marker : m.readW (off W d) 64 = BitVec.twoPow 64 k) :
    m.readW (off W d) 32 = BitVec.ofNat 32 (2 ^ k % 2 ^ 32) ∧
    m.readW (off W (d + 4)) 32 = BitVec.ofNat 32 (2 ^ k / 2 ^ 32) := by
  have value : (m.readW (off W d) 64).toNat = 2 ^ k := by
    rw [marker, BitVec.toNat_twoPow, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) bound)]
  constructor
  · apply BitVec.eq_of_toNat_eq
    rw [← VG.Proof.Rc2.Word32.readW64_lo, BitVec.extractLsb'_toNat, Nat.shiftRight_zero, value,
      BitVec.toNat_ofNat, Nat.mod_mod]
  · have address : off W (d + 4) = off W d + BitVec.ofNat 64 4 := by
      unfold off
      rw [BitVec.ofNat_add, BitVec.add_assoc]
    rw [address]
    apply BitVec.eq_of_toNat_eq
    rw [← VG.Proof.Rc2.Word32.readW64_hi, BitVec.extractLsb'_toNat, value, Nat.shiftRight_eq_div_pow,
      BitVec.toNat_ofNat]

theorem Entry.marker {s : State} (E : Entry s) :
    (entered s).mem.readW (off (wsOf s) ((geometry s).array 27 + 4 * (geometry s).words)) 32 =
      BitVec.ofNat 32 (2 ^ (mrA (initialValues s 0) % 64) % 2 ^ 32) ∧
    (entered s).mem.readW (off (wsOf s) ((geometry s).array 27 + 4 * (geometry s).words + 4)) 32 =
      BitVec.ofNat 32 (2 ^ (mrA (initialValues s 0) % 64) / 2 ^ 32) := by
  apply marker_halves (Nat.mod_lt _ (by decide))
  have fit : (geometry s).array 27 + 4 * (geometry s).words + 8 ≤ lenOf s := by
    have arrays := E.valid.arraysFit
    change Proof.Rsa.Mont.arrAt (geometry s).w 28 ≤ lenOf s at arrays
    unfold Geometry.array Geometry.words Proof.Rsa.Mont.arrAt Proof.Rsa.Mont.hdrBytes
    unfold Proof.Rsa.Mont.arrAt Proof.Rsa.Mont.hdrBytes at arrays
    omega
  rw [E.pushed_read fit]
  rw [show 4 * (geometry s).words = 8 * (geometry s).w by unfold Geometry.words; omega]
  exact E.prepared.2.2.2.2.2.2.2

end VG.Proof.MillerRabin.X86
