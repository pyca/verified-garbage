module

public import VerifiedGarbage.Proof.Dsa.Generation.WitnessBytes
public import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Omega

/-! # The forced-witness transformation in byte-addressed memory -/

@[expose] public section
namespace VG.Proof.Dsa.Generation
open VG VG.Proof.Bignum

private theorem off_eq_iff {p : Addr} {i j : Nat} (hi : i < 2 ^ 64) (hj : j < 2 ^ 64) :
    off p i = off p j ↔ i = j := by
  constructor
  · intro h
    have h' := congrArg (fun x => x - p) h
    simp only [off, Offset.add_sub_cancel_left] at h'
    have hv := congrArg BitVec.toNat h'
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using hv
  · intro h; rw [h]

theorem forcedWitness_memory (m : Mem) (p : Addr) {len : Nat}
    (hlen : 2 ≤ len) (hmax : len < 2 ^ 64) :
    Spec.Rsa.bytesAt ((m.writeW p (m p &&& (127 : Byte))).writeW
      (off p (len - 1)) (m (off p (len - 1)) ||| (2 : Byte))) p len =
        forcedWitnessBytes (Spec.Rsa.bytesAt m p len) := by
  apply List.ext_getElem
  · rw [bytesAt_length, forcedWitnessBytes_length (by simpa only [bytesAt_length] using hlen), bytesAt_length]
  · intro i hi hi'
    have hil : i < len := by simpa only [bytesAt_length] using hi
    have hget := forcedWitnessBytes_getD
      (bs := Spec.Rsa.bytesAt m p len) (i := i) (by simpa only [bytesAt_length] using hlen)
      (by simpa only [bytesAt_length] using hil)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some] at hget
    rw [hget]
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range,
      List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hil,
      Option.map_some, Option.getD_some, List.getElem?_range (show 0 < len by omega)]
    change ((m.writeW p (m p &&& (127 : Byte))).writeW
      (off p (len - 1)) (m (off p (len - 1)) ||| (2 : Byte))) (off p i) = _
    rw [WriteBytes.writeW8_apply, WriteBytes.writeW8_apply]
    have hlast := off_eq_iff (p := p) (i := i) (j := len - 1) (by omega) (by omega)
    have hzero : off p i = p ↔ i = 0 := by
      simpa only [off, BitVec.add_zero] using
        (off_eq_iff (p := p) (i := i) (j := 0) (by omega) (by decide))
    simp only [hlast, hzero, List.length_map, List.length_range]
    by_cases he : i = len - 1
    · subst i; simp
    · simp only [he, ite_false]
      by_cases hz : i = 0
      · subst i; simp
      · simp [hz, off]

end VG.Proof.Dsa.Generation
