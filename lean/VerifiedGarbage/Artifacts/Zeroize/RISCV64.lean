module

public import VerifiedGarbage.Proof.Zeroize.RISCV64
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Zeroization on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Zeroize.RISCV64

def artifacts : List Artifact := [
  Spec.Zeroize.zeroizeApi.artifact RISCV64.target {
    code := Impl.Zeroize.RISCV64.zeroize
    verified := Proof.Zeroize.RISCV64.verified }]

end VG.Artifacts.Zeroize.RISCV64
