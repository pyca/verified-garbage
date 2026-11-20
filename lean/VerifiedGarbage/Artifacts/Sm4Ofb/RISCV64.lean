module

public import VerifiedGarbage.Proof.Sm4.RISCV64.Scrub
public import VerifiedGarbage.Impl.Sm4.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Sm4.RISCV64.ModesLit
import VerifiedGarbage.Proof.Sm4.RISCV64.FbFinalLit

/-! # SM4-OFB on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Sm4Ofb.RISCV64

def artifacts : List Artifact := [
  Spec.Sm4.ofbApi.artifact RISCV64.target {
    code := Impl.Sm4.RISCV64.Fn.ofb
    verified := .scrubbed Proof.Sm4.RISCV64.Scrub.ofb_scrubbed },
  Spec.Sm4.ofbFinalApi.artifact RISCV64.target {
    code := Impl.Sm4.RISCV64.Fn.ofbFinal
    verified := .scrubbed Proof.Sm4.RISCV64.Scrub.ofbFinal_scrubbed }]

end VG.Artifacts.Sm4Ofb.RISCV64
