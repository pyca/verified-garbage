module

public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Backend
public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Verified

/-! # The verified baseline prepared round on RISC-V -/

@[expose] public section
namespace VG.Proof.Variants.MillerRabin.RISCV64.Base
open VG VG.RISCV64 VG.Proof.MillerRabin.RISCV64

def variant : RoundImpl where
  code := Impl.MillerRabin.RISCV64.round
  verified := round_verified
  stack := by decide +kernel
  suffix := ""
  features := []

end VG.Proof.Variants.MillerRabin.RISCV64.Base
