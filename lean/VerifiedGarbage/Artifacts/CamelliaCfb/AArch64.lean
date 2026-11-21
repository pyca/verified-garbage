module

public import VerifiedGarbage.Impl.Camellia.AArch64.Fn
public import VerifiedGarbage.Proof.Camellia.AArch64.FbVerified
public import VerifiedGarbage.Proof.Camellia.AArch64.FbFinalVerified
public import VerifiedGarbage.Proof.Camellia.AArch64.Residue
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.Camellia.AArch64.FbLit
import VerifiedGarbage.Proof.Camellia.AArch64.FbFinalLit

/-! # Camellia-CFB128 on AArch64 -/

@[expose] public section

namespace VG.Artifacts.CamelliaCfb.AArch64

def artifacts : List Artifact := [
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

end VG.Artifacts.CamelliaCfb.AArch64
