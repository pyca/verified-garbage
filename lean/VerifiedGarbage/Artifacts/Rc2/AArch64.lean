module

public import VerifiedGarbage.Proof.Rc2.AArch64.Cbc.Verified
public import VerifiedGarbage.Proof.Rc2.AArch64.Stream.Frame
public import VerifiedGarbage.Proof.Rc2.AArch64.Key
public import VerifiedGarbage.Proof.Rc2.AArch64.Cbc.Chained
public import VerifiedGarbage.Proof.Rc2.AArch64.CbcResidue
public import VerifiedGarbage.Proof.Rc2.AArch64.InitResidue
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print

/-! # RC2 on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Rc2.AArch64

def artifacts : List Artifact := [
  Spec.Rc2.cbcInitApi.artifact AArch64.target {
    code := Proof.Rc2.AArch64.InitResidue.cbcInitCode
    verified := .scrubbed ⟨Proof.Rc2.AArch64.InitResidue.cbcInitCode_verified,
      Proof.Rc2.AArch64.InitResidue.cbcInitCode_noResidue⟩ },
  Spec.Rc2.cbcEncryptChainedApi.artifact AArch64.target {
    code := Proof.Rc2.AArch64.CbcResidue.cbcEncryptChainedCode
    verified := .scrubbed ⟨Proof.Rc2.AArch64.CbcResidue.cbcEncryptChainedCode_verified,
      Proof.Rc2.AArch64.CbcResidue.cbcEncryptChainedCode_noResidue⟩ },
  Spec.Rc2.cbcDecryptChainedApi.artifact AArch64.target {
    code := Proof.Rc2.AArch64.CbcResidue.cbcDecryptChainedCode
    verified := .scrubbed ⟨Proof.Rc2.AArch64.CbcResidue.cbcDecryptChainedCode_verified,
      Proof.Rc2.AArch64.CbcResidue.cbcDecryptChainedCode_noResidue⟩ }]

end VG.Artifacts.Rc2.AArch64
