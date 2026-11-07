module
public import VerifiedGarbage.Proof.Rsa.AArch64.Guarded

import VerifiedGarbage.Proof.Rsa.AArch64.PdChecked
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Rsa.AArch64.ExpCheck
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Rsa.Contract

/-!
# `vg_rsa_public_checked` on AArch64: the leak of `n` and `e`

`leak_eq`: the leak of `n` and `e`, as bytes, determines each when `n`'s
length is the same.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Checked
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

/-- The leak of `n` and `e`, as bytes, determines each when `n`'s length is
the same. -/
theorem leak_eq {a b c d : List Byte} (hl : a.length = c.length)
    (h : (a ++ b).map (·.toNat) = (c ++ d).map (·.toNat)) : a = c ∧ b = d := by
  have hi : (a ++ b) = (c ++ d) := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h
  exact List.append_inj hi hl

end VG.Proof.Rsa.AArch64
