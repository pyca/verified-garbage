module

public import VerifiedGarbage.Proof.Rc2.AArch64.Cbc.Verified
public import VerifiedGarbage.Proof.Rc2.AArch64.Stream.Frame
public import VerifiedGarbage.Proof.Rc2.AArch64.Key
public import VerifiedGarbage.Proof.Rc2.AArch64.Cbc.Chained
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print

/-! # RC2 on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Rc2.AArch64

def artifacts : List Artifact := [
  Spec.Rc2.cbcInitApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 576 .x6 72 Impl.Rc2.AArch64.Stream.init
    stack := 592
    verified := Proof.Rc2.AArch64.Stream.init_framed },
  Spec.Rc2.cbcEncryptChainedApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 512 .x4 64 Impl.Rc2.AArch64.Cbc.encrypt
    stack := 512
    verified := Proof.Rc2.AArch64.Cbc.encryptChained_framed },
  Spec.Rc2.cbcDecryptChainedApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 512 .x4 64 Impl.Rc2.AArch64.Cbc.decrypt
    stack := 512
    verified := Proof.Rc2.AArch64.Cbc.decryptChained_framed }]

end VG.Artifacts.Rc2.AArch64
