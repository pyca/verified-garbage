module

public import VerifiedGarbage.Proof.TripleDes.RISCV64.ModesVerified
public import VerifiedGarbage.Proof.TripleDes.RISCV64.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.TripleDes.RISCV64.ModesLit
import VerifiedGarbage.Proof.TripleDes.RISCV64.FbFinalLit

/-! # Triple DES-OFB artifacts on baseline RISC-V -/

@[expose] public section

namespace VG.Artifacts.TripleDesOfb.RISCV64

def artifacts : List Artifact := [
  Spec.TripleDes.ofbApi.artifact RISCV64.target {
    code := Impl.TripleDes.RISCV64.ofb
    stack := 944
    verified := Proof.TripleDes.RISCV64.Modes.ofb_verified },
  Spec.TripleDes.ofbFinalApi.artifact RISCV64.target {
    code := Impl.TripleDes.RISCV64.ofbFinal
    stack := 944
    verified := Proof.TripleDes.RISCV64.Modes.ofbFinal_verified }]

end VG.Artifacts.TripleDesOfb.RISCV64
