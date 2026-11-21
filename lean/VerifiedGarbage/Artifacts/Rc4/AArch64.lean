module

public import VerifiedGarbage.Impl.Rc4.AArch64.Fn
public import VerifiedGarbage.Proof.Rc4.AArch64.VerifiedInit
public import VerifiedGarbage.Proof.Rc4.AArch64.VerifiedApply
public import VerifiedGarbage.Proof.Rc4.AArch64.Residue
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print

/-! # RC4 on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Rc4.AArch64

def artifacts : List Artifact := [
  Spec.Rc4.initApi.artifact AArch64.target {
    code := Impl.Rc4.AArch64.Fn.init
    verified := Proof.Rc4.AArch64.initCleared_scrubbed },
  Spec.Rc4.applyApi.artifact AArch64.target {
    code := Impl.Rc4.AArch64.Fn.apply
    verified := Proof.Rc4.AArch64.applyCleared_scrubbed }]

end VG.Artifacts.Rc4.AArch64
