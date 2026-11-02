module

import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Code
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.CTCode
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Implies
public import VerifiedGarbage.Proof.Rsa.AArch64.InvLaw
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.RsaKeyGen.AArch64.Key
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Spec.RsaKeyGen.Contract
public import VerifiedGarbage.TCB.AArch64.Target

/-!
# `vg_rsa_keygen_key` on AArch64: verified against the shared contract

With correctness (`keyCode_correct`), constant time (`keyCode_constantTime`)
and the shared contract's implication (`key_implies`), `code` is verified
(`key_verified`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64

/-- `vg_rsa_keygen_key`. -/
theorem key_verified [VG.Proof.Rsa.AArch64.InvLaw] :
    Verified target VG.Impl.RsaKeyGen.AArch64.Key.code (Spec.RsaKeyGen.keyContract abi) :=
  Verified.of_correct keyCode_correct keyCode_constantTime key_implies

end VG.Proof.RsaKeyGen.AArch64.Key
