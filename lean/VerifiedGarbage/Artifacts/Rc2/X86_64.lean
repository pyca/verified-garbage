module

public import VerifiedGarbage.Proof.Rc2.X86_64.Stream.Frame
public import VerifiedGarbage.Proof.Rc2.X86_64.Cbc.Verified
public import VerifiedGarbage.Proof.Rc2.X86_64.Key
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Rc2.X86_64.Stream.Lit

/-! # RC2 artifacts on baseline x86-64 -/

@[expose] public section

namespace VG.Artifacts.Rc2.X86_64

def artifacts : List Artifact := [
  Spec.Rc2.cbcInitApi.artifact X86_64.target {
    notes := ["Baseline x86-64: checks the lengths, copies the IV and calls the verified RC2 key expansion."]
    code := Impl.StackScratch.X86_64.withStackArgScratchWiped 592 0 72 Impl.Rc2.X86_64.Stream.init
    stack := 600
    verified := Proof.Rc2.X86_64.Stream.init_framed },
  Spec.Rc2.cbcEncryptUpdateApi.artifact X86_64.target {
    notes := ["Baseline x86-64: copies the pending and new bytes a byte at a time, then calls the verified RC2-CBC encryption on the complete blocks."]
    code := Impl.StackScratch.X86_64.withStackArgScratchWiped 592 0 72 Impl.Rc2.X86_64.Stream.encryptUpdate
    stack := 608
    verified := Proof.Rc2.X86_64.Stream.encryptUpdate_framed },
  Spec.Rc2.cbcDecryptUpdateApi.artifact X86_64.target {
    notes := ["Baseline x86-64: copies the pending and new bytes a byte at a time, then calls the verified RC2-CBC decryption on the complete blocks."]
    code := Impl.StackScratch.X86_64.withStackArgScratchWiped 592 0 72 Impl.Rc2.X86_64.Stream.decryptUpdate
    stack := 608
    verified := Proof.Rc2.X86_64.Stream.decryptUpdate_framed },
  Spec.Rc2.cbcEncryptApi.artifact X86_64.target {
    notes := ["Baseline x86-64, calling the verified RC2 block primitive."]
    code := Impl.Rc2.X86_64.Cbc.encrypt
    stack := 8
    verified := Proof.Rc2.X86_64.Cbc.encrypt_verified },
  Spec.Rc2.cbcDecryptApi.artifact X86_64.target {
    notes := ["Baseline x86-64, preserving the input ciphertext for the next IV."]
    code := Impl.Rc2.X86_64.Cbc.decrypt
    stack := 8
    verified := Proof.Rc2.X86_64.Cbc.decrypt_verified },
  Spec.Rc2.expandKeyApi.artifact X86_64.target {
    notes := ["Baseline x86-64 SSE2. PITABLE selection scans all 256 candidates in a fixed order, eight candidates per vector."]
    code := Impl.Rc2.X86_64.expandKey
    stack := 0
    verified := Proof.Rc2.X86_64.key_verified },
  Spec.Rc2.encryptBlockApi.artifact X86_64.target {
    notes := ["Baseline x86-64 SSE2. Mashing scans all 64 schedule words in a fixed order, eight words per vector."]
    code := Impl.Rc2.X86_64.encryptBlock
    stack := 0
    verified := Proof.Rc2.X86_64.encrypt_verified },
  Spec.Rc2.decryptBlockApi.artifact X86_64.target {
    notes := ["Baseline x86-64 SSE2. Reverse mashing scans all 64 schedule words in a fixed order, eight words per vector."]
    code := Impl.Rc2.X86_64.decryptBlock
    stack := 0
    verified := Proof.Rc2.X86_64.decrypt_verified }]

end VG.Artifacts.Rc2.X86_64
