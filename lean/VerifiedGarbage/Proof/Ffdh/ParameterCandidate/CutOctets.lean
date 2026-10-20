module
public import VerifiedGarbage.Spec.Rsa

import VerifiedGarbage.Proof.Ffdh.KeyScalar
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Bignum.Math

/-! # FFDH parameter candidates: witness bytes represent the specified masked draw -/

@[expose] public section

namespace VG.Proof.Ffdh.ParameterCandidate

open VG VG.Proof.Bignum

/-- The witness cut preserves every byte after the first. -/
def cutOctets (bs : List Byte) (j : Nat) : List Byte :=
  ((bs.getD 0 0) &&& BitVec.ofNat 8 (2 ^ (j + 1) - 1)) :: bs.drop 1

theorem cutOctets_length {bs : List Byte} (hne : bs ≠ []) (j : Nat) : (cutOctets bs j).length = bs.length := by
  simp only [cutOctets, List.length_cons, List.length_drop]
  have := List.length_pos_iff.mpr hne
  omega

theorem cutOctets_value {bs : List Byte} (hne : bs ≠ []) {j bits : Nat} (hj : j < 8)
    (hb : bits = 8 * (bs.length - 1) + j + 1) :
    Spec.Rsa.os2ip (cutOctets bs j) = Spec.Rsa.os2ip bs % 2 ^ bits := by
  have he : cutOctets bs j = KeyScalar.cut bs 0 (BitVec.ofNat 8 (2 ^ (j + 1) - 1)) := by
    simp only [cutOctets, KeyScalar.cut, List.replicate_zero, List.nil_append, Nat.zero_add]
  have hp : 2 ^ (j + 1) ≤ 256 := show 2 ^ (j + 1) ≤ 2 ^ 8 from Nat.pow_le_pow_right (by decide) (by omega)
  have hv : (BitVec.ofNat 8 (2 ^ (j + 1) - 1)).toNat = 2 ^ (j + 1) - 1 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hc := KeyScalar.cut_value (r := bs) (n := 0) (e := bs.length) (j := j + 1) (by omega)
    (List.length_pos_iff.mpr hne) (by omega) hv
  rw [he]
  simpa only [Nat.add_assoc, hb] using hc

end VG.Proof.Ffdh.ParameterCandidate
