module

public import VerifiedGarbage.Proof.Rc4.AArch64.VerifiedInit
public import VerifiedGarbage.Proof.Rc4.AArch64.VerifiedApply
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Raw RC4 on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.Rc4.AArch64

def artifacts : List Artifact := [
  Spec.Rc4.initApi.artifact AArch64.target {
    code := Impl.Rc4.AArch64.init
    verified := Proof.Rc4.AArch64.init_verified },
  Spec.Rc4.applyApi.artifact AArch64.target {
    code := Impl.Rc4.AArch64.apply
    verified := Proof.Rc4.AArch64.apply_verified }]

end VG.Artifacts.Rc4.AArch64
