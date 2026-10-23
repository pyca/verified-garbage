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
    notes := ["Copies the IV and calls the verified key expansion. The return address and our caller's \
        r25 are kept in the last 64 bytes of the working space on the stack, zeroed before returning."]
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 608 .r9 72 Impl.Rc2.PPC64LE.Stream.init
    stack := 608
    verified := Proof.Rc2.PPC64LE.Stream.init_framed },
  Spec.Rc2.cbcEncryptUpdateApi.artifact PPC64LE.target {
    notes := ["Copies bytes one at a time and calls the verified CBC encryption on the complete \
        blocks. The return address and our caller's r25 are kept in the last 64 bytes of the working \
        space on the stack, zeroed before returning."]
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 608 .r9 72 Impl.Rc2.PPC64LE.Stream.encryptUpdate
    stack := 608
    verified := Proof.Rc2.PPC64LE.Stream.encryptUpdate_framed },
  Spec.Rc2.cbcDecryptUpdateApi.artifact PPC64LE.target {
    notes := ["Copies bytes one at a time and calls the verified CBC decryption on the complete \
        blocks. The return address and our caller's r25 are kept in the last 64 bytes of the working \
        space on the stack, zeroed before returning."]
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 608 .r9 72 Impl.Rc2.PPC64LE.Stream.decryptUpdate
    stack := 608
    verified := Proof.Rc2.PPC64LE.Stream.decryptUpdate_framed },
  Spec.Rc2.cbcEncryptApi.artifact PPC64LE.target {
    notes := ["Calls the verified block encryption on each block in turn. Our caller's r26-r31 and \
        the return address are kept in the working space."]
    code := Impl.Rc2.PPC64LE.Cbc.encrypt
    stack := 0
    verified := Proof.Rc2.PPC64LE.Cbc.encrypt_verified },
  Spec.Rc2.cbcDecryptApi.artifact PPC64LE.target {
    notes := ["Calls the verified block decryption on each block in turn, keeping the input \
        ciphertext for the next IV. Our caller's r26-r31 and the return address are kept in the \
        working space."]
    code := Impl.Rc2.PPC64LE.Cbc.decrypt
    stack := 0
    verified := Proof.Rc2.PPC64LE.Cbc.decrypt_verified },
  Spec.Rc2.expandKeyApi.artifact PPC64LE.target {
    notes := ["PITABLE is written from immediates into the working space, and each lookup reads \
        all 32 of its doublewords, keeping the one that holds the index under a mask computed from \
        it. Our caller's r14 and r15 are kept in the working space."]
    code := Impl.Rc2.PPC64LE.expandKey
    stack := 0
    verified := Proof.Rc2.PPC64LE.key_verified },
  Spec.Rc2.encryptBlockApi.artifact PPC64LE.target {
    notes := ["The four words in general-purpose registers. Mashing reads all 16 doublewords of the \
        schedule, keeping the one that holds the index under a mask computed from it."]
    code := Impl.Rc2.PPC64LE.encryptBlock
    stack := 0
    verified := Proof.Rc2.PPC64LE.encrypt_verified },
  Spec.Rc2.decryptBlockApi.artifact PPC64LE.target {
    notes := ["The four words in general-purpose registers. Reverse mashing reads all 16 \
        doublewords of the schedule, keeping the one that holds the index under a mask computed \
        from it."]
    code := Impl.Rc2.PPC64LE.decryptBlock
    stack := 0
    verified := Proof.Rc2.PPC64LE.decrypt_verified }]

end VG.Artifacts.Rc2.PPC64LE
