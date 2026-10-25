module

public import VerifiedGarbage.Proof.Blowfish.RISCV64.EcbVerified
public import VerifiedGarbage.Proof.Blowfish.RISCV64.KeyVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Blowfish.RISCV64.Lit

/-! # Blowfish on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Blowfish.RISCV64

def artifacts : List Artifact := [
  Spec.Blowfish.expandKeyApi.artifact RISCV64.target {
    notes := ["The schedule is built in a frame of 4176 bytes on the stack, which is 16-byte \
        aligned, since the contract states no alignment for it: the initial schedule is written \
        from 1042 immediates, the P-array keyed a byte of the key at a time, and the 521 \
        encryptions run ECB's block function under the schedule as it is written. It is then \
        copied out a byte at a time, and the frame is zeroed before returning."]
    code := Impl.Blowfish.RISCV64.expandKey
    stack := 4176
    verified := Proof.Blowfish.RISCV64.expandKey_verified },
  Spec.Blowfish.ecbEncryptApi.artifact RISCV64.target {
    notes := ["The schedule is copied a byte at a time into a frame of 4176 bytes on the stack, \
        which is 16-byte aligned, since the contract states no alignment for it; the frame is \
        zeroed before returning. Nothing is allocated for no blocks.",
      "One block at a time in general-purpose registers: each S-box lookup reads the 256 \
        entries of its four byte planes, a word (four entries) of each at a time, keeping the bytes \
        of the entry that is the index under masks computed from it, so no address depends on the \
        data or the schedule."]
    code := Impl.Blowfish.RISCV64.encrypt
    stack := 4176
    verified := Proof.Blowfish.RISCV64.encrypt_verified },
  Spec.Blowfish.ecbDecryptApi.artifact RISCV64.target {
    notes := ["The schedule is copied a byte at a time into a frame of 4176 bytes on the stack, \
        which is 16-byte aligned, since the contract states no alignment for it; the frame is \
        zeroed before returning. Nothing is allocated for no blocks.",
      "One block at a time in general-purpose registers: each S-box lookup reads the 256 \
        entries of its four byte planes, a word (four entries) of each at a time, keeping the bytes \
        of the entry that is the index under masks computed from it, so no address depends on the \
        data or the schedule."]
    code := Impl.Blowfish.RISCV64.decrypt
    stack := 4176
    verified := Proof.Blowfish.RISCV64.decrypt_verified }]

end VG.Artifacts.Blowfish.RISCV64
