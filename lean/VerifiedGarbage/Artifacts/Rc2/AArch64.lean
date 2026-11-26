module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Rc2.Contract
import VerifiedGarbage.Impl.Rc2.AArch64.Fn
import VerifiedGarbage.Proof.Rc2.AArch64.Cbc.Verified
import VerifiedGarbage.Proof.Rc2.AArch64.Stream.Frame
import VerifiedGarbage.Proof.Rc2.AArch64.Key
import VerifiedGarbage.Proof.Rc2.AArch64.Cbc.Chained
import VerifiedGarbage.Proof.Rc2.AArch64.CbcResidue
import VerifiedGarbage.Proof.Rc2.AArch64.InitResidue
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # RC2 on AArch64 -/

namespace VG.Artifacts.Rc2.AArch64

public def artifacts : List (Artifact AArch64.target) := [
  Spec.Rc2.cbcInitApi.artifact AArch64.target {
    code := Impl.Rc2.AArch64.Fn.cbcInit
    verified := Proof.Rc2.AArch64.InitResidue.cbcInitCode_scrubbed },
  Spec.Rc2.cbcEncryptChainedApi.artifact AArch64.target {
    code := Impl.Rc2.AArch64.Fn.cbcEncryptChained
    verified := Proof.Rc2.AArch64.CbcResidue.cbcEncryptChainedCode_scrubbed },
  Spec.Rc2.cbcDecryptChainedApi.artifact AArch64.target {
    code := Impl.Rc2.AArch64.Fn.cbcDecryptChained
    verified := Proof.Rc2.AArch64.CbcResidue.cbcDecryptChainedCode_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Rc2.AArch64
