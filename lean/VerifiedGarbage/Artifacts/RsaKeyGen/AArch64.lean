module

public import VerifiedGarbage.Proof.Rsa.AArch64.Instances
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Verified
public import Aesop.BuiltinRules
import Mathlib.Tactic.Finiteness.Attr
public import VerifiedGarbage.Proof.Framework.Registration

/-! # RSA key generation (FIPS 186-5 A.1.3) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.RsaKeyGen.AArch64

def artifacts : List Artifact := [
  Spec.RsaKeyGen.keyApi.artifact AArch64.target {
    code := Impl.RsaKeyGen.AArch64.Key.code
    verified := Proof.RsaKeyGen.AArch64.Key.key_verified }]

end VG.Artifacts.RsaKeyGen.AArch64
