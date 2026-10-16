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
    notes := ["Baseline AArch64: copies the IV and calls the verified key expansion, saving the \
        link register in a 16-byte stack frame."]
    code := Impl.StackScratch.AArch64.withStackScratchWiped 576 .x6 72 Impl.Rc2.AArch64.Stream.init
    stack := 592
    verified := Proof.Rc2.AArch64.Stream.init_framed },
  Spec.Rc2.cbcEncryptUpdateApi.artifact AArch64.target {
    notes := ["Baseline AArch64: copies bytes one at a time and calls the verified CBC \
        encryption on the complete blocks, saving the link register in a 16-byte stack frame."]
    code := Impl.StackScratch.AArch64.withStackScratchWiped 576 .x6 72 Impl.Rc2.AArch64.Stream.encryptUpdate
    stack := 592
    verified := Proof.Rc2.AArch64.Stream.encryptUpdate_framed },
  Spec.Rc2.cbcDecryptUpdateApi.artifact AArch64.target {
    notes := ["Baseline AArch64: copies bytes one at a time and calls the verified CBC \
        decryption on the complete blocks, saving the link register in a 16-byte stack frame."]
    code := Impl.StackScratch.AArch64.withStackScratchWiped 576 .x6 72 Impl.Rc2.AArch64.Stream.decryptUpdate
    stack := 592
    verified := Proof.Rc2.AArch64.Stream.decryptUpdate_framed },
  Spec.Rc2.cbcEncryptApi.artifact AArch64.target {
    notes := ["Baseline AArch64, calling the verified RC2 block primitive."]
    code := Impl.Rc2.AArch64.Cbc.encrypt
    stack := 0
    verified := Proof.Rc2.AArch64.Cbc.encrypt_verified },
  Spec.Rc2.cbcDecryptApi.artifact AArch64.target {
    notes := ["Baseline AArch64. Groups of eight blocks are decrypted together in AdvSIMD \
        registers, each word of four blocks in the 32-bit lanes of one register, with the \
        schedule in `v16`–`v23` for key-word broadcasts and the mashing's `tbl` lookups; the \
        blocks left are decrypted one at a time by the block primitive, preserving the input \
        ciphertext for the next IV."]
    code := Impl.Rc2.AArch64.Cbc.decrypt
    stack := 0
    verified := Proof.Rc2.AArch64.Cbc.decrypt_verified },
  Spec.Rc2.expandKeyApi.artifact AArch64.target {
    notes := ["Baseline AArch64. Each PITABLE lookup builds the table in `v16`–`v31` from \
        immediates and selects from it with four `tbl`s."]
    code := Impl.Rc2.AArch64.expandKey
    stack := 0
    verified := Proof.Rc2.AArch64.key_verified },
  Spec.Rc2.encryptBlockApi.artifact AArch64.target {
    notes := ["Baseline AArch64. Mashing loads the schedule into `v16`–`v23` and selects a word \
        from it with two `tbl`s."]
    code := Impl.Rc2.AArch64.encryptBlock
    stack := 0
    verified := Proof.Rc2.AArch64.encrypt_verified },
  Spec.Rc2.decryptBlockApi.artifact AArch64.target {
    notes := ["Baseline AArch64. Reverse mashing loads the schedule into `v16`–`v23` and \
        selects a word from it with two `tbl`s."]
    code := Impl.Rc2.AArch64.decryptBlock
    stack := 0
    verified := Proof.Rc2.AArch64.decrypt_verified }]

end VG.Artifacts.Rc2.AArch64
