module

public import VerifiedGarbage.Proof.Variants.MillerRabin.RISCV64.Base

/-! # The implementations of `MillerRabin` on RISC-V (RV64) -/

@[expose] public section

namespace VG.Proof.Variants.MillerRabin.RISCV64

def base : Proof.MillerRabin.RISCV64.RoundImpl := Proof.Variants.MillerRabin.RISCV64.Base.variant

/-- Every implementation, which each function generic over them is emitted
with (the registration files that import this). -/
def variants := [base]

end VG.Proof.Variants.MillerRabin.RISCV64
