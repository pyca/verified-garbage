module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Camellia.Cfb
public import VerifiedGarbage.Spec.Camellia.CfbFinal
import VerifiedGarbage.Impl.Camellia.AArch64.Fn
import VerifiedGarbage.Proof.Camellia.AArch64.FbVerified
import VerifiedGarbage.Proof.Camellia.AArch64.FbFinalVerified
import VerifiedGarbage.Proof.Camellia.AArch64.Residue
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Camellia.AArch64.FbLit
import VerifiedGarbage.Proof.Camellia.AArch64.FbFinalLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Camellia-CFB128 on AArch64 -/

namespace VG.Artifacts.CamelliaCfb.AArch64

public def artifacts : List (Artifact AArch64.target) := [
  Spec.Camellia.cfbEncryptApi.artifact AArch64.target {
    code := Impl.Camellia.AArch64.Fn.cfbEncrypt
    verified := Proof.Camellia.AArch64.Residue.cfbEncryptCode_scrubbed },
  Spec.Camellia.cfbDecryptApi.artifact AArch64.target {
    code := Impl.Camellia.AArch64.Fn.cfbDecrypt
    verified := Proof.Camellia.AArch64.Residue.cfbDecryptCode_scrubbed },
  Spec.Camellia.cfbEncryptFinalApi.artifact AArch64.target {
    code := Impl.Camellia.AArch64.Fn.cfbEncryptFinal
    verified := Proof.Camellia.AArch64.Residue.cfbEncryptFinalCode_scrubbed },
  Spec.Camellia.cfbDecryptFinalApi.artifact AArch64.target {
    code := Impl.Camellia.AArch64.Fn.cfbDecryptFinal
    verified := Proof.Camellia.AArch64.Residue.cfbDecryptFinalCode_scrubbed }]

spec_apis artifacts

end VG.Artifacts.CamelliaCfb.AArch64
