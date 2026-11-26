module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Blowfish.Cfb
public import VerifiedGarbage.Spec.Blowfish.CfbFinal
import VerifiedGarbage.Impl.Blowfish.AArch64.Fn
import VerifiedGarbage.Proof.Blowfish.AArch64.FbVerified
import VerifiedGarbage.Proof.Blowfish.AArch64.FbFinalVerified
import VerifiedGarbage.Proof.Blowfish.AArch64.ModesResidue
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Blowfish.AArch64.ModesLit
import VerifiedGarbage.Proof.Blowfish.AArch64.FbFinalLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Blowfish-CFB64 on AArch64 -/

namespace VG.Artifacts.BlowfishCfb.AArch64

public def artifacts : List (Artifact AArch64.target) := [
  Spec.Blowfish.cfbEncryptApi.artifact AArch64.target {
    code := Impl.Blowfish.AArch64.Fn.cfbEncrypt
    verified := Proof.Blowfish.AArch64.ModesResidue.cfbEncryptCode_scrubbed },
  Spec.Blowfish.cfbDecryptApi.artifact AArch64.target {
    code := Impl.Blowfish.AArch64.Fn.cfbDecrypt
    verified := Proof.Blowfish.AArch64.ModesResidue.cfbDecryptCode_scrubbed },
  Spec.Blowfish.cfbEncryptFinalApi.artifact AArch64.target {
    code := Impl.Blowfish.AArch64.Fn.cfbEncryptFinal
    verified := Proof.Blowfish.AArch64.ModesResidue.cfbEncryptFinalCode_scrubbed },
  Spec.Blowfish.cfbDecryptFinalApi.artifact AArch64.target {
    code := Impl.Blowfish.AArch64.Fn.cfbDecryptFinal
    verified := Proof.Blowfish.AArch64.ModesResidue.cfbDecryptFinalCode_scrubbed }]

spec_apis artifacts

end VG.Artifacts.BlowfishCfb.AArch64
