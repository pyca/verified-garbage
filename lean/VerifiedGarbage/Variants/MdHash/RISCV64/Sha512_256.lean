module

public import VerifiedGarbage.Proof.HmacTable.RISCV64

/-! # SHA-512/256 on RISC-V -/

@[expose] public section

namespace VG.Variants.MdHash.RISCV64.Sha512_256

def variant : Proof.HmacTable.RISCV64.HVar := Proof.HmacTable.RISCV64.sha512_256W

end VG.Variants.MdHash.RISCV64.Sha512_256
