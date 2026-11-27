module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Camellia.Cbc
import VerifiedGarbage.Impl.Camellia.AArch64.Fn
import VerifiedGarbage.Proof.Camellia.AArch64.CbcVerified
import VerifiedGarbage.Proof.Camellia.AArch64.Residue
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Camellia-CBC on AArch64 -/

namespace VG.Artifacts.CamelliaCbc.AArch64

public def artifacts : List (Artifact AArch64.target) := [
  Spec.Camellia.cbcEncryptChainedApi.artifact AArch64.target {
    code := Impl.Camellia.AArch64.Fn.cbcEncryptChained
    verified := Proof.Camellia.AArch64.Residue.cbcEncryptChainedCode_scrubbed },
  Spec.Camellia.cbcDecryptChainedApi.artifact AArch64.target {
    code := Impl.Camellia.AArch64.Fn.cbcDecryptChained
    verified := Proof.Camellia.AArch64.Residue.cbcDecryptChainedCode_scrubbed }]

spec_apis artifacts

end VG.Artifacts.CamelliaCbc.AArch64
