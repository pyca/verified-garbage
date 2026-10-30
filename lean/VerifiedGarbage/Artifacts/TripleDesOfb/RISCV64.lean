module

public import VerifiedGarbage.Proof.TripleDes.RISCV64.ModesVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.TripleDes.RISCV64.ModesLit

/-! # Triple DES-OFB artifacts on baseline RISC-V -/

@[expose] public section

namespace VG.Artifacts.TripleDesOfb.RISCV64

def artifacts : List Artifact := [
  Spec.TripleDes.ofbApi.artifact RISCV64.target {
    code := Impl.TripleDes.RISCV64.ofb
    stack := 944
    verified := Proof.TripleDes.RISCV64.Modes.ofb_verified }]

end VG.Artifacts.TripleDesOfb.RISCV64
