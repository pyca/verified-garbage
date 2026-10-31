module

public import VerifiedGarbage.Proof.Rc2.AArch64.Cbc.Verified
public import VerifiedGarbage.Proof.Rc2.AArch64.Stream.Frame
public import VerifiedGarbage.Proof.Rc2.AArch64.Key
public import VerifiedGarbage.Proof.Framework.Registration

/-! # RC2 artifacts on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.Rc2.AArch64

def artifacts : List Artifact := [
  Spec.Rc2.cbcInitApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 576 .x6 72 Impl.Rc2.AArch64.Stream.init
    stack := 592
    verified := Proof.Rc2.AArch64.Stream.init_framed },
  Spec.Rc2.cbcEncryptUpdateApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 576 .x6 72 Impl.Rc2.AArch64.Stream.encryptUpdate
    stack := 592
    verified := Proof.Rc2.AArch64.Stream.encryptUpdate_framed },
  Spec.Rc2.cbcDecryptUpdateApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 576 .x6 72 Impl.Rc2.AArch64.Stream.decryptUpdate
    stack := 592
    verified := Proof.Rc2.AArch64.Stream.decryptUpdate_framed },
  Spec.Rc2.cbcEncryptApi.artifact AArch64.target {
    code := Impl.Rc2.AArch64.Cbc.encrypt
    stack := 0
    verified := Proof.Rc2.AArch64.Cbc.encrypt_verified },
  Spec.Rc2.cbcDecryptApi.artifact AArch64.target {
    code := Impl.Rc2.AArch64.Cbc.decrypt
    stack := 0
    verified := Proof.Rc2.AArch64.Cbc.decrypt_verified },
  Spec.Rc2.expandKeyApi.artifact AArch64.target {
    code := Impl.Rc2.AArch64.expandKey
    stack := 0
    verified := Proof.Rc2.AArch64.key_verified },
  Spec.Rc2.encryptBlockApi.artifact AArch64.target {
    code := Impl.Rc2.AArch64.encryptBlock
    stack := 0
    verified := Proof.Rc2.AArch64.encrypt_verified },
  Spec.Rc2.decryptBlockApi.artifact AArch64.target {
    code := Impl.Rc2.AArch64.decryptBlock
    stack := 0
    verified := Proof.Rc2.AArch64.decrypt_verified }]

end VG.Artifacts.Rc2.AArch64
