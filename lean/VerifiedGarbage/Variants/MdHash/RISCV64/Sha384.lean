module

public import VerifiedGarbage.Proof.HmacTable.RISCV64

/-! # SHA-384 on RISC-V -/

@[expose] public section

namespace VG.Variants.MdHash.RISCV64.Sha384

def variant : Proof.HmacTable.RISCV64.HVar := Proof.HmacTable.RISCV64.sha384W

end VG.Variants.MdHash.RISCV64.Sha384
