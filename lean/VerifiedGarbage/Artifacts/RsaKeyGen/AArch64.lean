module

public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.KeyInit
public import VerifiedGarbage.Spec.RsaKeyGen.KeySearchContract
import Mathlib.Tactic.Finiteness.Attr
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print

/-! # RSA key generation (FIPS 186-5 A.1.3) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.RsaKeyGen.AArch64

def artifacts : List Artifact := [
  Spec.RsaKeyGen.keyInitApi.artifact AArch64.target {
    code := Impl.RsaKeyGen.AArch64.KeyInit.init
    verified := Proof.RsaKeyGen.AArch64.KeyInit.init_verified }]

end VG.Artifacts.RsaKeyGen.AArch64
