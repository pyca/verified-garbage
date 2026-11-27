module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Sm4.Cbc
import VerifiedGarbage.Impl.Sm4.AArch64.Fn
import VerifiedGarbage.Proof.Sm4.AArch64.CbcVerified
import VerifiedGarbage.Proof.Sm4.AArch64.Sm4e.Modes
import VerifiedGarbage.Proof.Sm4.AArch64.Sm4e.Chained
import VerifiedGarbage.Proof.Sm4.AArch64.ModesResidue
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SM4-CBC on AArch64 -/

namespace VG.Artifacts.Sm4Cbc.AArch64

public def artifacts : List (Artifact AArch64.target) := [
  Spec.Sm4.cbcEncryptChainedApi.artifact AArch64.target {
    suffix := "_sm4"
    code := Impl.Sm4.AArch64.Fn.cbcEncryptChainedSm4
    verified := Proof.Sm4.AArch64.ModesResidue.cbcEncryptChainedSm4Code_scrubbed },
  Spec.Sm4.cbcEncryptChainedApi.artifact AArch64.target {
    code := Impl.Sm4.AArch64.Fn.cbcEncryptChained
    verified := Proof.Sm4.AArch64.ModesResidue.cbcEncryptChainedCode_scrubbed },
  Spec.Sm4.cbcDecryptChainedApi.artifact AArch64.target {
    suffix := "_sm4"
    code := Impl.Sm4.AArch64.Fn.cbcDecryptChainedSm4
    verified := Proof.Sm4.AArch64.ModesResidue.cbcDecryptChainedSm4Code_scrubbed },
  Spec.Sm4.cbcDecryptChainedApi.artifact AArch64.target {
    code := Impl.Sm4.AArch64.Fn.cbcDecryptChained
    verified := Proof.Sm4.AArch64.ModesResidue.cbcDecryptChainedCode_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Sm4Cbc.AArch64
