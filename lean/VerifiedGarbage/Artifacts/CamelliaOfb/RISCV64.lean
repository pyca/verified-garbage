module

public import VerifiedGarbage.Proof.Camellia.RISCV64.Scrub
public import VerifiedGarbage.Impl.Camellia.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Camellia.RISCV64.ModesLit
import VerifiedGarbage.Proof.Camellia.RISCV64.FbFinalLit

/-! # Camellia-OFB on RISC-V -/

@[expose] public section

namespace VG.Artifacts.CamelliaOfb.RISCV64

def artifacts : List Artifact := [
  Spec.Camellia.ofbApi.artifact RISCV64.target {
    code := Impl.Camellia.RISCV64.Fn.ofb
    verified := .scrubbed Proof.Camellia.RISCV64.Scrub.ofb_scrubbed },
  Spec.Camellia.ofbFinalApi.artifact RISCV64.target {
    code := Impl.Camellia.RISCV64.Fn.ofbFinal
    verified := .scrubbed Proof.Camellia.RISCV64.Scrub.ofbFinal_scrubbed }]

end VG.Artifacts.CamelliaOfb.RISCV64
