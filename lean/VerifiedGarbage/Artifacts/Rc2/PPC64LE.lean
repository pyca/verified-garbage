module

public import VerifiedGarbage.Proof.Rc2.PPC64LE.Block
public import VerifiedGarbage.Proof.Rc2.PPC64LE.KeyVerified
public import VerifiedGarbage.Proof.Rc2.PPC64LE.Cbc.Verified
public import VerifiedGarbage.Proof.Rc2.PPC64LE.Stream.Frame
public import VerifiedGarbage.Proof.Framework.Registration

/-! # RC2 artifacts on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Rc2.PPC64LE

def artifacts : List Artifact := [
  Spec.Rc2.cbcInitApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 608 .r9 72 Impl.Rc2.PPC64LE.Stream.init
    stack := 608
    verified := Proof.Rc2.PPC64LE.Stream.init_framed },
  Spec.Rc2.cbcEncryptUpdateApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 608 .r9 72 Impl.Rc2.PPC64LE.Stream.encryptUpdate
    stack := 608
    verified := Proof.Rc2.PPC64LE.Stream.encryptUpdate_framed },
  Spec.Rc2.cbcDecryptUpdateApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 608 .r9 72 Impl.Rc2.PPC64LE.Stream.decryptUpdate
    stack := 608
    verified := Proof.Rc2.PPC64LE.Stream.decryptUpdate_framed },
  Spec.Rc2.cbcEncryptApi.artifact PPC64LE.target {
    code := Impl.Rc2.PPC64LE.Cbc.encrypt
    stack := 0
    verified := Proof.Rc2.PPC64LE.Cbc.encrypt_verified },
  Spec.Rc2.cbcDecryptApi.artifact PPC64LE.target {
    code := Impl.Rc2.PPC64LE.Cbc.decrypt
    stack := 0
    verified := Proof.Rc2.PPC64LE.Cbc.decrypt_verified },
  Spec.Rc2.expandKeyApi.artifact PPC64LE.target {
    code := Impl.Rc2.PPC64LE.expandKey
    stack := 0
    verified := Proof.Rc2.PPC64LE.key_verified },
  Spec.Rc2.encryptBlockApi.artifact PPC64LE.target {
    code := Impl.Rc2.PPC64LE.encryptBlock
    stack := 0
    verified := Proof.Rc2.PPC64LE.encrypt_verified },
  Spec.Rc2.decryptBlockApi.artifact PPC64LE.target {
    code := Impl.Rc2.PPC64LE.decryptBlock
    stack := 0
    verified := Proof.Rc2.PPC64LE.decrypt_verified }]

end VG.Artifacts.Rc2.PPC64LE
