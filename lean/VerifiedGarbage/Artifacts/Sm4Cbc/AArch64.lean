module

public import VerifiedGarbage.Impl.Sm4.AArch64.Fn
public import VerifiedGarbage.Proof.Sm4.AArch64.CbcVerified
public import VerifiedGarbage.Proof.Sm4.AArch64.Sm4e.Modes
public import VerifiedGarbage.Proof.Sm4.AArch64.Sm4e.Chained
public import VerifiedGarbage.Proof.Sm4.AArch64.ModesResidue
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print

/-! # SM4-CBC on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Sm4Cbc.AArch64

def artifacts : List Artifact := [
  Spec.Sm4.cbcEncryptChainedApi.artifact AArch64.target {
    suffix := "_sm4"
    code := Impl.Sm4.AArch64.Fn.cbcEncryptChainedSm4
    verified := .scrubbed Proof.Sm4.AArch64.ModesResidue.cbcEncryptChainedSm4Code_scrubbed },
  Spec.Sm4.cbcEncryptChainedApi.artifact AArch64.target {
    code := Impl.Sm4.AArch64.Fn.cbcEncryptChained
    verified := .scrubbed Proof.Sm4.AArch64.ModesResidue.cbcEncryptChainedCode_scrubbed },
  Spec.Sm4.cbcDecryptChainedApi.artifact AArch64.target {
    suffix := "_sm4"
    code := Impl.Sm4.AArch64.Fn.cbcDecryptChainedSm4
    verified := .scrubbed Proof.Sm4.AArch64.ModesResidue.cbcDecryptChainedSm4Code_scrubbed },
  Spec.Sm4.cbcDecryptChainedApi.artifact AArch64.target {
    code := Impl.Sm4.AArch64.Fn.cbcDecryptChained
    verified := .scrubbed Proof.Sm4.AArch64.ModesResidue.cbcDecryptChainedCode_scrubbed }]

end VG.Artifacts.Sm4Cbc.AArch64
