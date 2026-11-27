module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Seed.Contract
import VerifiedGarbage.Impl.Seed.AArch64.Fn
import VerifiedGarbage.Proof.Seed.AArch64.Frame
import VerifiedGarbage.Proof.Seed.AArch64.EcbCall
import VerifiedGarbage.Proof.Seed.AArch64.Verified
import VerifiedGarbage.Proof.Seed.AArch64.ModesResidue
import VerifiedGarbage.Proof.Seed.AArch64.EcbResidue
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SEED on AArch64 -/

namespace VG.Artifacts.Seed.AArch64

public def artifacts : List (Artifact AArch64.target) := [
  Spec.Seed.expandKeyApi.artifact AArch64.target {
    code := Impl.Seed.AArch64.Fn.expandKey
    verified := Proof.Seed.AArch64.ModesResidue.expandKeyCode_scrubbed },
  Spec.Seed.ecbEncryptApi.artifact AArch64.target {
    code := Impl.Seed.AArch64.Fn.ecbEncrypt
    verified := Proof.Seed.AArch64.EcbResidue.ecbEncryptCode_scrubbed },
  Spec.Seed.ecbDecryptApi.artifact AArch64.target {
    code := Impl.Seed.AArch64.Fn.ecbDecrypt
    verified := Proof.Seed.AArch64.EcbResidue.ecbDecryptCode_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Seed.AArch64
