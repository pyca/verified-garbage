module

public import VerifiedGarbage.Proof.TripleDes.RISCV64.Key.Verified
public import VerifiedGarbage.Proof.TripleDes.RISCV64.EcbVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.TripleDes.RISCV64.FunctionsLit

/-! # Triple DES on RISC-V -/

@[expose] public section

namespace VG.Artifacts.TripleDes.RISCV64

def artifacts : List Artifact := [
  Spec.TripleDes.expandKeyApi.artifact RISCV64.target {
    notes := ["Scalar key expansion with fixed bit permutations (one bit at a time, by shifts and \
        masks) and public round-count branches, in temporaries and argument registers only. The key \
        and the schedule are accessed a byte at a time, since the contract states no alignment for \
        them."]
    code := Impl.TripleDes.RISCV64.Key.expandKey
    verified := Proof.TripleDes.RISCV64.Key.verified },
  Spec.TripleDes.ecbEncryptApi.artifact RISCV64.target {
    notes := ["One block at a time in general-purpose registers, with IP and FP shared across the \
        three DES passes. Each round looks the eight S-boxes up at once in the 64 \
        lanes of a word: E of R and the round key are unpacked into a byte per S-box, each lane's \
        six input bits are spread into masks, and a multiplexer tree over 32 words of constants \
        selects every lane's table entry; P moves the outputs in groups by shift distance.",
      "The schedules are copied a byte at a time into a frame of 944 bytes on the stack, which is \
        16-byte aligned, since the contract states no alignment for them; the frame also holds the \
        callee-saved registers the rounds use and the rounds' 55 words of constants, which each \
        block stores first, and is zeroed before returning. Nothing is allocated for no blocks."]
    code := Impl.TripleDes.RISCV64.Ecb.encrypt
    stack := 944
    verified := Proof.TripleDes.RISCV64.Ecb.encrypt_verified },
  Spec.TripleDes.ecbDecryptApi.artifact RISCV64.target {
    notes := ["One block at a time in general-purpose registers, with IP and FP shared across the \
        three DES passes, with the reverse EDE key order. Each round looks the eight S-boxes up at once in the 64 \
        lanes of a word: E of R and the round key are unpacked into a byte per S-box, each lane's \
        six input bits are spread into masks, and a multiplexer tree over 32 words of constants \
        selects every lane's table entry; P moves the outputs in groups by shift distance.",
      "The schedules are copied a byte at a time into a frame of 944 bytes on the stack, which is \
        16-byte aligned, since the contract states no alignment for them; the frame also holds the \
        callee-saved registers the rounds use and the rounds' 55 words of constants, which each \
        block stores first, and is zeroed before returning. Nothing is allocated for no blocks."]
    code := Impl.TripleDes.RISCV64.Ecb.decrypt
    stack := 944
    verified := Proof.TripleDes.RISCV64.Ecb.decrypt_verified }]

end VG.Artifacts.TripleDes.RISCV64
