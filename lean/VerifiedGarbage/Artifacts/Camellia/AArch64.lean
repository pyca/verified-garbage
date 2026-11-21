module

public import VerifiedGarbage.Impl.Camellia.AArch64.Fn
public import VerifiedGarbage.Proof.Camellia.AArch64.Verified
public import VerifiedGarbage.Proof.Camellia.AArch64.KeyVerified
public import VerifiedGarbage.Proof.Camellia.AArch64.Serial.Verified
public import VerifiedGarbage.Proof.Camellia.AArch64.Lit
public import VerifiedGarbage.Proof.Camellia.AArch64.Residue
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print

/-! # Camellia on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Camellia.AArch64

def artifacts : List Artifact := [
  Spec.Camellia.expandKeyApi.artifact AArch64.target {
    code := Impl.Camellia.AArch64.Fn.expandKey
    verified := Proof.Camellia.AArch64.Residue.expandKeyCode_scrubbed },
  Spec.Camellia.ecbEncryptApi.artifact AArch64.target {
    code := Impl.Camellia.AArch64.Fn.ecbEncrypt
    verified := Proof.Camellia.AArch64.Residue.ecbEncryptCode_scrubbed },
  Spec.Camellia.ecbDecryptApi.artifact AArch64.target {
    code := Impl.Camellia.AArch64.Fn.ecbDecrypt
    verified := Proof.Camellia.AArch64.Residue.ecbDecryptCode_scrubbed }]

end VG.Artifacts.Camellia.AArch64
