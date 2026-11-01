module

public import VerifiedGarbage.Proof.Camellia.RISCV64.ModesVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Camellia.RISCV64.ModesLit

/-! # Camellia-OFB artifacts on baseline RISC-V -/

@[expose] public section

namespace VG.Artifacts.CamelliaOfb.RISCV64

def artifacts : List Artifact := [
  Spec.Camellia.ofbApi.artifact RISCV64.target {
    code := Impl.Camellia.RISCV64.ofb
    stack := 3248
    verified := Proof.Camellia.RISCV64.Modes.ofb_verified }]

end VG.Artifacts.CamelliaOfb.RISCV64
