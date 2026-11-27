module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Blowfish.Contract
import VerifiedGarbage.Impl.Blowfish.AArch64.Fn
import VerifiedGarbage.Proof.Blowfish.AArch64.KeyVerified
import VerifiedGarbage.Proof.Blowfish.AArch64.Residue
import VerifiedGarbage.Proof.Blowfish.AArch64.Frame
import VerifiedGarbage.Proof.Blowfish.AArch64.Verified
import VerifiedGarbage.Proof.Blowfish.AArch64.ModesResidue
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Blowfish on AArch64 -/

namespace VG.Artifacts.Blowfish.AArch64

public def artifacts : List (Artifact AArch64.target) := [
  Spec.Blowfish.expandKeyApi.artifact AArch64.target {
    code := Impl.Blowfish.AArch64.Fn.expandKey
    verified := Proof.Blowfish.AArch64.expandKeyCleared_scrubbed },
  Spec.Blowfish.ecbEncryptApi.artifact AArch64.target {
    code := Impl.Blowfish.AArch64.Fn.ecbEncrypt
    verified := Proof.Blowfish.AArch64.ModesResidue.ecbEncryptCode_scrubbed },
  Spec.Blowfish.ecbDecryptApi.artifact AArch64.target {
    code := Impl.Blowfish.AArch64.Fn.ecbDecrypt
    verified := Proof.Blowfish.AArch64.ModesResidue.ecbDecryptCode_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Blowfish.AArch64
