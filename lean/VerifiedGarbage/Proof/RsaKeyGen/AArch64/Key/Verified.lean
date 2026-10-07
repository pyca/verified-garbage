import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Code
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.CTCode
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Implies
import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_rsa_keygen_key` on AArch64: verified against the shared contract

With correctness (`keyCode_correct`), constant time (`keyCode_constantTime`)
and the shared contract's implication (`key_implies`), `code` is verified
(`key_verified`).
-/

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64

/-- `vg_rsa_keygen_key`. -/
theorem key_verified :
    Verified target VG.Impl.RsaKeyGen.AArch64.Key.code (Spec.RsaKeyGen.keyContract abi) :=
  Verified.of_correct keyCode_correct keyCode_constantTime key_implies

end VG.Proof.RsaKeyGen.AArch64.Key
