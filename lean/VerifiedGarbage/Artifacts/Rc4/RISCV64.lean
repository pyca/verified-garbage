module

public import VerifiedGarbage.Proof.Rc4.RISCV64.Verified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Rc4.RISCV64.Lit

/-! # Raw RC4 on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Rc4.RISCV64

def artifacts : List Artifact := [
  Spec.Rc4.initApi.artifact RISCV64.target {
    notes := ["The table is built in a frame of 256 bytes on the stack, which is 16-byte \
      aligned, then copied to the context a byte at a time, since the contract states no \
      alignment for it; the frame is zeroed before returning.",
      "The table is visited as 32 doublewords at fixed addresses: a secret-indexed read \
      keeps, with masks, the doubleword and then the byte that hold it, and a write stores \
      every doubleword back XORed with a masked difference, so no address or branch depends \
      on the key, the table or `j`."]
    code := Impl.Rc4.RISCV64.init
    stack := 256
    verified := Proof.Rc4.RISCV64.init_verified },
  Spec.Rc4.applyApi.artifact RISCV64.target {
    notes := ["The table is copied a byte at a time to a frame of 256 bytes on the stack, \
      which is 16-byte aligned, since the contract states no alignment for the context, \
      updated there and copied back; the frame is zeroed before returning.",
      "The table is visited as 32 doublewords at fixed addresses: a secret-indexed read \
      keeps, with masks, the doubleword and then the byte that hold it, and a write stores \
      every doubleword back XORed with a masked difference, so no address or branch depends \
      on the table, `j` or the data."]
    code := Impl.Rc4.RISCV64.apply
    stack := 256
    verified := Proof.Rc4.RISCV64.apply_verified }]

end VG.Artifacts.Rc4.RISCV64
