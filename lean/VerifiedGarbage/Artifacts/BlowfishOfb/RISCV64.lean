module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Blowfish.Ofb
public import VerifiedGarbage.Spec.Blowfish.OfbFinal
import VerifiedGarbage.Proof.Blowfish.RISCV64.Scrub
import VerifiedGarbage.Impl.Blowfish.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Blowfish.RISCV64.ModesLit
import VerifiedGarbage.Proof.Blowfish.RISCV64.FbFinalLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Blowfish-OFB on RISC-V -/

namespace VG.Artifacts.BlowfishOfb.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Blowfish.ofbApi.artifact RISCV64.target {
    code := Impl.Blowfish.RISCV64.Fn.ofb
    verified := Proof.Blowfish.RISCV64.Scrub.ofb_scrubbed },
  Spec.Blowfish.ofbFinalApi.artifact RISCV64.target {
    code := Impl.Blowfish.RISCV64.Fn.ofbFinal
    verified := Proof.Blowfish.RISCV64.Scrub.ofbFinal_scrubbed }]

spec_apis artifacts

end VG.Artifacts.BlowfishOfb.RISCV64
