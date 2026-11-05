module

public import VerifiedGarbage.Proof.HmacTable.RISCV64

/-! # MD5 on RISC-V -/

@[expose] public section

namespace VG.Variants.MdHash.RISCV64.Md5

def variant : Proof.HmacTable.RISCV64.HVar := Proof.HmacTable.RISCV64.md5W

end VG.Variants.MdHash.RISCV64.Md5
