module

public import VerifiedGarbage.Proof.Blowfish.RISCV64.ModesVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Blowfish.RISCV64.ModesLit

/-! # Blowfish-OFB artifacts on baseline RISC-V -/

@[expose] public section

namespace VG.Artifacts.BlowfishOfb.RISCV64

def artifacts : List Artifact := [
  Spec.Blowfish.ofbApi.artifact RISCV64.target {
    code := Impl.Blowfish.RISCV64.ofb
    stack := 4224
    verified := Proof.Blowfish.RISCV64.Modes.ofb_verified }]

end VG.Artifacts.BlowfishOfb.RISCV64
