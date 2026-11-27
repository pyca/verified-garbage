module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Rc4.Contract
import VerifiedGarbage.Impl.Rc4.AArch64.Fn
import VerifiedGarbage.Proof.Rc4.AArch64.VerifiedInit
import VerifiedGarbage.Proof.Rc4.AArch64.VerifiedApply
import VerifiedGarbage.Proof.Rc4.AArch64.Residue
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # RC4 on AArch64 -/

namespace VG.Artifacts.Rc4.AArch64

public def artifacts : List (Artifact AArch64.target) := [
  Spec.Rc4.initApi.artifact AArch64.target {
    code := Impl.Rc4.AArch64.Fn.init
    verified := Proof.Rc4.AArch64.initCleared_scrubbed },
  Spec.Rc4.applyApi.artifact AArch64.target {
    code := Impl.Rc4.AArch64.Fn.apply
    verified := Proof.Rc4.AArch64.applyCleared_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Rc4.AArch64
