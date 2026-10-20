module
public import VerifiedGarbage.Spec.Dsa

import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Fixed-width encodings used by the DSA entry points -/

@[expose] public section

namespace VG.Proof.Dsa
open VG

theorem encodeBE_length (k value : Nat) : (Spec.Dsa.encodeBE k value).length = k := by
  rw [encodeBE_i2osp, VG.Proof.Rsa.i2osp_length]

theorem decodeBE_encodeBE {k value : Nat} (h : value < 256 ^ k) :
    Spec.Dsa.decodeBE (Spec.Dsa.encodeBE k value) = value := by
  rw [encodeBE_i2osp, decodeBE_os2ip, VG.Proof.Rsa.os2ip_i2osp, Nat.mod_eq_of_lt h]

theorem encodeBE_decodeBE (bytes : List Byte) : Spec.Dsa.encodeBE bytes.length (Spec.Dsa.decodeBE bytes) = bytes := by
  rw [encodeBE_i2osp, decodeBE_os2ip, VG.Proof.Rsa.i2osp_os2ip]

theorem decodeBE_lt (bytes : List Byte) : Spec.Dsa.decodeBE bytes < 256 ^ bytes.length :=
  VG.Proof.Rsa.lt_of_os2ip bytes

theorem encodeBE_eq_bytes {bytes : List Byte} {k value : Nat} (hlen : bytes.length = k)
    (hfit : value < 256 ^ k) : Spec.Dsa.encodeBE k value = bytes ↔ value = Spec.Dsa.decodeBE bytes := by
  constructor
  · intro h
    have hd := congrArg Spec.Dsa.decodeBE h
    rw [decodeBE_encodeBE hfit] at hd
    exact hd
  · intro h
    rw [h, ← hlen, encodeBE_decodeBE]

end VG.Proof.Dsa
