module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Seed.Cfb
public import VerifiedGarbage.Spec.Seed.CfbFinal
import VerifiedGarbage.Impl.Seed.AArch64.Fn
import VerifiedGarbage.Proof.Seed.AArch64.FbVerified
import VerifiedGarbage.Proof.Seed.AArch64.FbFinalVerified
import VerifiedGarbage.Proof.Seed.AArch64.ModesResidue
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Seed.AArch64.ModesLit
import VerifiedGarbage.Proof.Seed.AArch64.FbFinalLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SEED-CFB128 on AArch64 -/

namespace VG.Artifacts.SeedCfb.AArch64

public def artifacts : List (Artifact AArch64.target) := [
  Spec.Seed.cfbEncryptApi.artifact AArch64.target {
    code := Impl.Seed.AArch64.Fn.cfbEncrypt
    verified := Proof.Seed.AArch64.ModesResidue.cfbEncryptCode_scrubbed },
  Spec.Seed.cfbDecryptApi.artifact AArch64.target {
    code := Impl.Seed.AArch64.Fn.cfbDecrypt
    verified := Proof.Seed.AArch64.ModesResidue.cfbDecryptCode_scrubbed },
  Spec.Seed.cfbEncryptFinalApi.artifact AArch64.target {
    code := Impl.Seed.AArch64.Fn.cfbEncryptFinal
    verified := Proof.Seed.AArch64.ModesResidue.cfbEncryptFinalCode_scrubbed },
  Spec.Seed.cfbDecryptFinalApi.artifact AArch64.target {
    code := Impl.Seed.AArch64.Fn.cfbDecryptFinal
    verified := Proof.Seed.AArch64.ModesResidue.cfbDecryptFinalCode_scrubbed }]

spec_apis artifacts

end VG.Artifacts.SeedCfb.AArch64
