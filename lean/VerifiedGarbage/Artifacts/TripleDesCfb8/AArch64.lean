module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.TripleDes.Cfb8
import VerifiedGarbage.Impl.TripleDes.AArch64.Fn
import VerifiedGarbage.Proof.TripleDes.AArch64.FbVerified
import VerifiedGarbage.Proof.TripleDes.AArch64.ModesResidue
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Triple DES-CFB8 on AArch64 -/

namespace VG.Artifacts.TripleDesCfb8.AArch64

public def artifacts : List (Artifact AArch64.target) := [
  Spec.TripleDes.cfb8EncryptApi.artifact AArch64.target {
    code := Impl.TripleDes.AArch64.Fn.cfb8Encrypt
    verified := Proof.TripleDes.AArch64.ModesResidue.cfb8EncryptCode_scrubbed },
  Spec.TripleDes.cfb8DecryptApi.artifact AArch64.target {
    code := Impl.TripleDes.AArch64.Fn.cfb8Decrypt
    verified := Proof.TripleDes.AArch64.ModesResidue.cfb8DecryptCode_scrubbed }]

spec_apis artifacts

end VG.Artifacts.TripleDesCfb8.AArch64
