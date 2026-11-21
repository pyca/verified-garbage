module

public import VerifiedGarbage.Impl.Rc2.AArch64.Fn
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
    code := Impl.Rc2.AArch64.Fn.cbcInit
    verified := Proof.Rc2.AArch64.InitResidue.cbcInitCode_scrubbed },
  Spec.Rc2.cbcEncryptChainedApi.artifact AArch64.target {
    code := Impl.Rc2.AArch64.Fn.cbcEncryptChained
    verified := Proof.Rc2.AArch64.CbcResidue.cbcEncryptChainedCode_scrubbed },
  Spec.Rc2.cbcDecryptChainedApi.artifact AArch64.target {
    code := Impl.Rc2.AArch64.Fn.cbcDecryptChained
    verified := Proof.Rc2.AArch64.CbcResidue.cbcDecryptChainedCode_scrubbed }]

end VG.Artifacts.Rc2.AArch64
