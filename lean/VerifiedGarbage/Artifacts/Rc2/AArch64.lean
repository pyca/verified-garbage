import VerifiedGarbage.Proof.Rc2.AArch64.Block
import VerifiedGarbage.Proof.Rc2.AArch64.Key
import VerifiedGarbage.Proof.Rc2.AArch64.Cbc.Verified
import VerifiedGarbage.Proof.Rc2.AArch64.Stream.Frame

/-! # RC2 artifacts on baseline AArch64 -/

namespace VG.Artifacts.Rc2.AArch64

def artifacts : List Artifact := [
  { Spec.Rc2.cbcInitApi with
    target := AArch64.target
    doc := Spec.Rc2.cbcInitApi.doc
      (notes := ["Baseline AArch64: copies the IV and calls the verified key expansion, saving the \
        link register in a 16-byte stack frame."])
    code := Impl.StackScratch.AArch64.withStackScratchWiped 576 .x6 72 Impl.Rc2.AArch64.Stream.init
    contract := Spec.Rc2.cbcInitContract AArch64.abi 592
    stack := 592
    ofSig := ⟨_, _, _, by unfold Spec.Rc2.cbcInitContract; rfl⟩
    verified := Proof.Rc2.AArch64.Stream.init_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Rc2.cbcEncryptUpdateApi with
    target := AArch64.target
    doc := Spec.Rc2.cbcEncryptUpdateApi.doc
      (notes := ["Baseline AArch64: copies bytes one at a time and calls the verified CBC \
        encryption on the complete blocks, saving the link register in a 16-byte stack frame."])
    code := Impl.StackScratch.AArch64.withStackScratchWiped 576 .x6 72 Impl.Rc2.AArch64.Stream.encryptUpdate
    contract := Spec.Rc2.cbcEncryptUpdateContract AArch64.abi 592
    stack := 592
    ofSig := ⟨_, _, _, by unfold Spec.Rc2.cbcEncryptUpdateContract Spec.Rc2.cbcUpdateContract; rfl⟩
    verified := Proof.Rc2.AArch64.Stream.encryptUpdate_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Rc2.cbcDecryptUpdateApi with
    target := AArch64.target
    doc := Spec.Rc2.cbcDecryptUpdateApi.doc
      (notes := ["Baseline AArch64: copies bytes one at a time and calls the verified CBC \
        decryption on the complete blocks, saving the link register in a 16-byte stack frame."])
    code := Impl.StackScratch.AArch64.withStackScratchWiped 576 .x6 72 Impl.Rc2.AArch64.Stream.decryptUpdate
    contract := Spec.Rc2.cbcDecryptUpdateContract AArch64.abi 592
    stack := 592
    ofSig := ⟨_, _, _, by unfold Spec.Rc2.cbcDecryptUpdateContract Spec.Rc2.cbcUpdateContract; rfl⟩
    verified := Proof.Rc2.AArch64.Stream.decryptUpdate_framed
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Rc2.cbcEncryptApi with
    target := AArch64.target
    doc := Spec.Rc2.cbcEncryptApi.doc
      (notes := ["Baseline AArch64, calling the verified RC2 block primitive."])
    code := Impl.Rc2.AArch64.Cbc.encrypt
    contract := Spec.Rc2.cbcEncryptContract AArch64.abi 0
    stack := 0
    ofSig := ⟨_, _, _, by unfold Spec.Rc2.cbcEncryptContract Spec.Rc2.cbcContract; rfl⟩
    verified := Proof.Rc2.AArch64.Cbc.encrypt_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Rc2.cbcDecryptApi with
    target := AArch64.target
    doc := Spec.Rc2.cbcDecryptApi.doc
      (notes := ["Baseline AArch64. Groups of eight blocks are decrypted together in AdvSIMD \
        registers, each word of four blocks in the 32-bit lanes of one register, with the \
        schedule in `v16`–`v23` for key-word broadcasts and the mashing's `tbl` lookups; the \
        blocks left are decrypted one at a time by the block primitive, preserving the input \
        ciphertext for the next IV."])
    code := Impl.Rc2.AArch64.Cbc.decrypt
    contract := Spec.Rc2.cbcDecryptContract AArch64.abi 0
    stack := 0
    ofSig := ⟨_, _, _, by unfold Spec.Rc2.cbcDecryptContract Spec.Rc2.cbcContract; rfl⟩
    verified := Proof.Rc2.AArch64.Cbc.decrypt_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Rc2.expandKeyApi with
    target := AArch64.target
    doc := Spec.Rc2.expandKeyApi.doc
      (notes := ["Baseline AArch64. Each PITABLE lookup builds the table in `v16`–`v31` from \
        immediates and selects from it with four `tbl`s."])
    code := Impl.Rc2.AArch64.expandKey
    contract := Spec.Rc2.expandKeyContract AArch64.abi
    stack := 0
    verified := Proof.Rc2.AArch64.key_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Rc2.encryptBlockApi with
    target := AArch64.target
    doc := Spec.Rc2.encryptBlockApi.doc
      (notes := ["Baseline AArch64. Mashing loads the schedule into `v16`–`v23` and selects a word \
        from it with two `tbl`s."])
    code := Impl.Rc2.AArch64.encryptBlock
    contract := Spec.Rc2.encryptBlockContract AArch64.abi
    stack := 0
    verified := Proof.Rc2.AArch64.encrypt_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Rc2.decryptBlockApi with
    target := AArch64.target
    doc := Spec.Rc2.decryptBlockApi.doc
      (notes := ["Baseline AArch64. Reverse mashing loads the schedule into `v16`–`v23` and \
        selects a word from it with two `tbl`s."])
    code := Impl.Rc2.AArch64.decryptBlock
    contract := Spec.Rc2.decryptBlockContract AArch64.abi
    stack := 0
    verified := Proof.Rc2.AArch64.decrypt_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Rc2.AArch64
