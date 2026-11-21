module

public import VerifiedGarbage.Proof.TripleDes.RISCV64.Scrub
public import VerifiedGarbage.Impl.TripleDes.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.TripleDes.RISCV64.ModesLit
import VerifiedGarbage.Proof.TripleDes.RISCV64.FbFinalLit

/-! # Triple DES-OFB on RISC-V -/

@[expose] public section

namespace VG.Artifacts.TripleDesOfb.RISCV64

def artifacts : List Artifact := [
  Spec.TripleDes.ofbApi.artifact RISCV64.target {
    code := Impl.TripleDes.RISCV64.Fn.ofb
    verified := Proof.TripleDes.RISCV64.Scrub.ofb_scrubbed },
  Spec.TripleDes.ofbFinalApi.artifact RISCV64.target {
    code := Impl.TripleDes.RISCV64.Fn.ofbFinal
    verified := Proof.TripleDes.RISCV64.Scrub.ofbFinal_scrubbed }]

end VG.Artifacts.TripleDesOfb.RISCV64
