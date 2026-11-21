module

public import VerifiedGarbage.Impl.Seed.AArch64.Fn
public import VerifiedGarbage.Proof.Seed.AArch64.Frame
public import VerifiedGarbage.Proof.Seed.AArch64.EcbCall
public import VerifiedGarbage.Proof.Seed.AArch64.Verified
public import VerifiedGarbage.Proof.Seed.AArch64.ModesResidue
public import VerifiedGarbage.Proof.Seed.AArch64.EcbResidue
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print

/-! # SEED on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Seed.AArch64

def artifacts : List Artifact := [
  Spec.Seed.expandKeyApi.artifact AArch64.target {
    code := Impl.Seed.AArch64.Fn.expandKey
    verified := Proof.Seed.AArch64.ModesResidue.expandKeyCode_scrubbed },
  Spec.Seed.ecbEncryptApi.artifact AArch64.target {
    code := Impl.Seed.AArch64.Fn.ecbEncrypt
    verified := Proof.Seed.AArch64.EcbResidue.ecbEncryptCode_scrubbed },
  Spec.Seed.ecbDecryptApi.artifact AArch64.target {
    code := Impl.Seed.AArch64.Fn.ecbDecrypt
    verified := Proof.Seed.AArch64.EcbResidue.ecbDecryptCode_scrubbed }]

end VG.Artifacts.Seed.AArch64
