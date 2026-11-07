module

public import VerifiedGarbage.Proof.Camellia.RISCV64.ModesVerified
public import VerifiedGarbage.Proof.Camellia.RISCV64.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Camellia.RISCV64.ModesLit
import VerifiedGarbage.Proof.Camellia.RISCV64.FbFinalLit

/-! # Camellia-OFB artifacts on baseline RISC-V -/

@[expose] public section

namespace VG.Artifacts.CamelliaOfb.RISCV64

def artifacts : List Artifact := [
  Spec.Camellia.ofbApi.artifact RISCV64.target {
    code := Impl.Camellia.RISCV64.ofb
    stack := 3264
    verified := Proof.Camellia.RISCV64.Modes.ofb_verified },
  Spec.Camellia.ofbFinalApi.artifact RISCV64.target {
    code := Impl.Camellia.RISCV64.ofbFinal
    stack := 3264
    verified := Proof.Camellia.RISCV64.Modes.ofbFinal_verified }]

end VG.Artifacts.CamelliaOfb.RISCV64
