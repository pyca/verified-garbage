module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.TripleDes.Cfb
public import VerifiedGarbage.Spec.TripleDes.CfbFinal
import VerifiedGarbage.Impl.TripleDes.AArch64.Fn
import VerifiedGarbage.Proof.TripleDes.AArch64.FbVerified
import VerifiedGarbage.Proof.TripleDes.AArch64.FbFinalVerified
import VerifiedGarbage.Proof.TripleDes.AArch64.ModesResidue
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.TripleDes.AArch64.FbLit
import VerifiedGarbage.Proof.TripleDes.AArch64.FbFinalLit
import VerifiedGarbage.Proof.TripleDes.AArch64.ShortCfb
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Triple DES-CFB64 on AArch64 -/

namespace VG.Artifacts.TripleDesCfb.AArch64

public def artifacts : List (Artifact AArch64.target) := [
  Spec.TripleDes.cfbEncryptApi.artifact AArch64.target {
    code := Impl.TripleDes.AArch64.Fn.cfbEncrypt
    verified := Proof.TripleDes.AArch64.ModesResidue.cfbEncryptCode_scrubbed },
  Spec.TripleDes.cfbDecryptApi.artifact AArch64.target {
    code := Impl.TripleDes.AArch64.Fn.cfbDecrypt
    verified := Proof.TripleDes.AArch64.ModesResidue.cfbDecryptCode_scrubbed },
  Spec.TripleDes.cfbEncryptFinalApi.artifact AArch64.target {
    code := Impl.TripleDes.AArch64.Fn.cfbEncryptFinal
    verified := Proof.TripleDes.AArch64.ModesResidue.cfbEncryptFinalCode_scrubbed },
  Spec.TripleDes.cfbDecryptFinalApi.artifact AArch64.target {
    code := Impl.TripleDes.AArch64.Fn.cfbDecryptFinal
    verified := Proof.TripleDes.AArch64.ModesResidue.cfbDecryptFinalCode_scrubbed }]

spec_apis artifacts

end VG.Artifacts.TripleDesCfb.AArch64
