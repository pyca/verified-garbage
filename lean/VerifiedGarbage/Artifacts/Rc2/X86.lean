module

public import VerifiedGarbage.Proof.Rc2.X86.Key
public import VerifiedGarbage.Proof.Rc2.X86.Cbc.Verified
public import VerifiedGarbage.Proof.Rc2.X86.Stream.Frame
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Rc2.X86.Stream.Lit

/-! # RC2 artifacts on baseline x86 -/

@[expose] public section

namespace VG.Artifacts.Rc2.X86

def artifacts : List Artifact := [
  Spec.Rc2.cbcInitApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 608 6 144 Impl.Rc2.X86.Stream.init
    stack := 632
    verified := Proof.Rc2.X86.Stream.init_framed },
  Spec.Rc2.cbcEncryptUpdateApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 608 6 144 Impl.Rc2.X86.Stream.encryptUpdate
    stack := 648
    verified := Proof.Rc2.X86.Stream.encryptUpdate_framed },
  Spec.Rc2.cbcDecryptUpdateApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 608 6 144 Impl.Rc2.X86.Stream.decryptUpdate
    stack := 648
    verified := Proof.Rc2.X86.Stream.decryptUpdate_framed },
  Spec.Rc2.cbcEncryptApi.artifact X86.target {
    code := Impl.Rc2.X86.Cbc.encrypt
    stack := 16
    verified := Proof.Rc2.X86.Cbc.encrypt_verified },
  Spec.Rc2.cbcDecryptApi.artifact X86.target {
    code := Impl.Rc2.X86.Cbc.decrypt
    stack := 16
    verified := Proof.Rc2.X86.Cbc.decrypt_verified },
  Spec.Rc2.expandKeyApi.artifact X86.target {
    code := Impl.Rc2.X86.expandKey
    stack := 0
    verified := Proof.Rc2.X86.key_verified },
  Spec.Rc2.encryptBlockApi.artifact X86.target {
    code := Impl.Rc2.X86.encryptBlock
    stack := 0
    verified := Proof.Rc2.X86.encrypt_verified },
  Spec.Rc2.decryptBlockApi.artifact X86.target {
    code := Impl.Rc2.X86.decryptBlock
    stack := 0
    verified := Proof.Rc2.X86.decrypt_verified }]

end VG.Artifacts.Rc2.X86
