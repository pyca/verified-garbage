module

public import VerifiedGarbage.Proof.HmacTable.RISCV64

/-! # SHA-1 on RISC-V -/

@[expose] public section

namespace VG.Variants.MdHash.RISCV64.Sha1

def variant : Proof.HmacTable.RISCV64.HVar := Proof.HmacTable.RISCV64.sha1W

end VG.Variants.MdHash.RISCV64.Sha1
