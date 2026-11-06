module

public import VerifiedGarbage.Spec.Rsa

/-!
# The length of I2OSP

`i2osp x k` is `k` octets long (`i2osp_length`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig

open Spec.Rsa

theorem i2osp_length (x k : Nat) : (i2osp x k).length = k := by simp [i2osp]

end VG.Proof.RsaPkcs1Sig
