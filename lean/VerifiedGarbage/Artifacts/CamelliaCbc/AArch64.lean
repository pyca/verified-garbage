module

public import VerifiedGarbage.Impl.Camellia.AArch64.Fn
public import VerifiedGarbage.Proof.Camellia.AArch64.CbcVerified
public import VerifiedGarbage.Proof.Camellia.AArch64.Residue
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print

/-! # Camellia-CBC on AArch64 -/

@[expose] public section

namespace VG.Artifacts.CamelliaCbc.AArch64

def artifacts : List Artifact := [
  Spec.Camellia.cbcEncryptChainedApi.artifact AArch64.target {
    code := Impl.Camellia.AArch64.Fn.cbcEncryptChained
    verified := .scrubbed Proof.Camellia.AArch64.Residue.cbcEncryptChainedCode_scrubbed },
  Spec.Camellia.cbcDecryptChainedApi.artifact AArch64.target {
    code := Impl.Camellia.AArch64.Fn.cbcDecryptChained
    verified := .scrubbed Proof.Camellia.AArch64.Residue.cbcDecryptChainedCode_scrubbed }]

end VG.Artifacts.CamelliaCbc.AArch64
