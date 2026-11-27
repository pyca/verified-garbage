module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Aes.Contract
import VerifiedGarbage.Impl.Aes.AArch64.Fn
import VerifiedGarbage.Proof.Aes.AArch64.Aese.ExpandKey
import VerifiedGarbage.Proof.Aes.AArch64.Frame
import VerifiedGarbage.Proof.Aes.AArch64.ExpandKey
import VerifiedGarbage.Proof.Aes.AArch64.KeyResidue
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES (FIPS 197) on AArch64 -/

namespace VG.Artifacts.Aes.AArch64

public def artifacts : List (Artifact AArch64.target) := [
  Spec.Aes.expandKeyApi.artifact AArch64.target {
    code := Impl.Aes.AArch64.Fn.expandKey
    verified := Proof.Aes.AArch64.KeyResidue.expandKeyCode_scrubbed },
  Spec.Aes.expandKeyApi.artifact AArch64.target {
    suffix := "_aes"
    code := Impl.Aes.AArch64.Fn.expandKeyAes
    verified := Proof.Aes.AArch64.KeyResidue.expandKeyAesCode_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Aes.AArch64
