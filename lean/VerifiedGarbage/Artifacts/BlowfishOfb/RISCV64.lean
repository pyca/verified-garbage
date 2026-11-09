module

public import VerifiedGarbage.Proof.Blowfish.RISCV64.ModesVerified
public import VerifiedGarbage.Proof.Blowfish.RISCV64.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Blowfish.RISCV64.ModesLit
import VerifiedGarbage.Proof.Blowfish.RISCV64.FbFinalLit

/-! # Blowfish-OFB artifacts on baseline RISC-V -/

@[expose] public section

namespace VG.Artifacts.BlowfishOfb.RISCV64

def artifacts : List Artifact := [
  Spec.Blowfish.ofbApi.artifact RISCV64.target {
    code := Impl.Blowfish.RISCV64.ofb
    stack := 4240
    verified := Proof.Blowfish.RISCV64.Modes.ofb_verified },
  Spec.Blowfish.ofbFinalApi.artifact RISCV64.target {
    code := Impl.Blowfish.RISCV64.ofbFinal
    stack := 4240
    verified := Proof.Blowfish.RISCV64.Modes.ofbFinal_verified }]

end VG.Artifacts.BlowfishOfb.RISCV64
