module

public import VerifiedGarbage.Proof.Variants.MillerRabin.RISCV64.Base

/-! # The baseline shared Miller–Rabin round on RISC-V -/

@[expose] public section
namespace VG.Variants.MillerRabin.RISCV64.Base

def variant : Proof.MillerRabin.RISCV64.RoundImpl := Proof.Variants.MillerRabin.RISCV64.Base.variant

end VG.Variants.MillerRabin.RISCV64.Base
