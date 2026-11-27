module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Camellia.Contract
import VerifiedGarbage.Impl.Camellia.AArch64.Fn
import VerifiedGarbage.Proof.Camellia.AArch64.Verified
import VerifiedGarbage.Proof.Camellia.AArch64.KeyVerified
import VerifiedGarbage.Proof.Camellia.AArch64.Serial.Verified
import VerifiedGarbage.Proof.Camellia.AArch64.Lit
import VerifiedGarbage.Proof.Camellia.AArch64.Residue
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Camellia on AArch64 -/

namespace VG.Artifacts.Camellia.AArch64

public def artifacts : List (Artifact AArch64.target) := [
  Spec.Camellia.expandKeyApi.artifact AArch64.target {
    code := Impl.Camellia.AArch64.Fn.expandKey
    verified := Proof.Camellia.AArch64.Residue.expandKeyCode_scrubbed },
  Spec.Camellia.ecbEncryptApi.artifact AArch64.target {
    code := Impl.Camellia.AArch64.Fn.ecbEncrypt
    verified := Proof.Camellia.AArch64.Residue.ecbEncryptCode_scrubbed },
  Spec.Camellia.ecbDecryptApi.artifact AArch64.target {
    code := Impl.Camellia.AArch64.Fn.ecbDecrypt
    verified := Proof.Camellia.AArch64.Residue.ecbDecryptCode_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Camellia.AArch64
