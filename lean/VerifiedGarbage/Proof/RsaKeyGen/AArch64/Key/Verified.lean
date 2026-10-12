module

public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Code
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.CTCode
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Implies
public import VerifiedGarbage.Proof.Framework.Contract
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

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
theorem key_verified :
    Verified target VG.Impl.RsaKeyGen.AArch64.Key.code (Spec.RsaKeyGen.keyContract abi) :=
  Verified.of_correct keyCode_correct keyCode_constantTime key_implies

end VG.Proof.RsaKeyGen.AArch64.Key
