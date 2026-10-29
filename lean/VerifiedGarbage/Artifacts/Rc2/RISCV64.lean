module

public import VerifiedGarbage.Proof.Rc2.RISCV64.Block
public import VerifiedGarbage.Proof.Rc2.RISCV64.KeyVerified
public import VerifiedGarbage.Proof.Rc2.RISCV64.Cbc.Verified
public import VerifiedGarbage.Proof.Rc2.RISCV64.Stream.Frame
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Rc2.RISCV64.Lit
import VerifiedGarbage.Proof.Rc2.RISCV64.Cbc.Lit
import VerifiedGarbage.Proof.Rc2.RISCV64.Stream.Lit

/-! # RC2 artifacts on baseline RISC-V -/

@[expose] public section

namespace VG.Artifacts.Rc2.RISCV64

def artifacts : List Artifact := [
  Spec.Rc2.cbcInitApi.artifact RISCV64.target {
    notes := ["Copies the IV and calls the verified key expansion. The return address and our caller's \
        s7 are kept in the last 64 bytes of the working space on the stack, zeroed before returning."]
    code := Impl.StackScratch.RISCV64.withStackScratchWiped 608 .a6 72 Impl.Rc2.RISCV64.Stream.init
    stack := 608
    verified := Proof.Rc2.RISCV64.Stream.init_framed },
  Spec.Rc2.cbcEncryptUpdateApi.artifact RISCV64.target {
    notes := ["Copies bytes one at a time and calls the verified CBC encryption on the complete \
        blocks. The return address and our caller's s7 are kept in the last 64 bytes of the working \
        space on the stack, zeroed before returning."]
    code := Impl.StackScratch.RISCV64.withStackScratchWiped 608 .a6 72 Impl.Rc2.RISCV64.Stream.encryptUpdate
    stack := 608
    verified := Proof.Rc2.RISCV64.Stream.encryptUpdate_framed },
  Spec.Rc2.cbcDecryptUpdateApi.artifact RISCV64.target {
    notes := ["Copies bytes one at a time and calls the verified CBC decryption on the complete \
        blocks. The return address and our caller's s7 are kept in the last 64 bytes of the working \
        space on the stack, zeroed before returning."]
    code := Impl.StackScratch.RISCV64.withStackScratchWiped 608 .a6 72 Impl.Rc2.RISCV64.Stream.decryptUpdate
    stack := 608
    verified := Proof.Rc2.RISCV64.Stream.decryptUpdate_framed },
  Spec.Rc2.cbcEncryptApi.artifact RISCV64.target {
    notes := ["Calls the verified block encryption on each block in turn, reading and writing the IV \
        and the data a byte at a time. Our caller's s1-s6 and the return address are kept in the \
        working space."]
    code := Impl.Rc2.RISCV64.Cbc.encrypt
    stack := 0
    verified := Proof.Rc2.RISCV64.Cbc.encrypt_verified },
  Spec.Rc2.cbcDecryptApi.artifact RISCV64.target {
    notes := ["Calls the verified block decryption on each block in turn, keeping the input \
        ciphertext for the next IV, and reading and writing the IV and the data a byte at a time. Our \
        caller's s1-s6 and the return address are kept in the working space."]
    code := Impl.Rc2.RISCV64.Cbc.decrypt
    stack := 0
    verified := Proof.Rc2.RISCV64.Cbc.decrypt_verified },
  Spec.Rc2.expandKeyApi.artifact RISCV64.target {
    notes := ["PITABLE is written from immediates into the working space, and each lookup reads \
        all 32 of its doublewords, keeping the one that holds the index under a mask computed from \
        it. The key and the schedule are accessed a byte at a time."]
    code := Impl.Rc2.RISCV64.expandKey
    stack := 0
    verified := Proof.Rc2.RISCV64.key_verified },
  Spec.Rc2.encryptBlockApi.artifact RISCV64.target {
    notes := ["The schedule is copied a byte at a time to the working space, which is aligned, and \
        the four words are kept in general-purpose registers. Mashing reads all 16 doublewords of the \
        copy, keeping the one that holds the index under a mask computed from it."]
    code := Impl.Rc2.RISCV64.encryptBlock
    stack := 0
    verified := Proof.Rc2.RISCV64.encrypt_verified },
  Spec.Rc2.decryptBlockApi.artifact RISCV64.target {
    notes := ["The schedule is copied a byte at a time to the working space, which is aligned, and \
        the four words are kept in general-purpose registers. Reverse mashing reads all 16 \
        doublewords of the copy, keeping the one that holds the index under a mask computed from \
        it."]
    code := Impl.Rc2.RISCV64.decryptBlock
    stack := 0
    verified := Proof.Rc2.RISCV64.decrypt_verified }]

end VG.Artifacts.Rc2.RISCV64
