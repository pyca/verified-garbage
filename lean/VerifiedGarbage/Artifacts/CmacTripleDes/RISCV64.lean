module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Cmac.TripleDesContract
import VerifiedGarbage.Proof.CmacTripleDes.Stream.RISCV64.Frame
import VerifiedGarbage.Impl.CmacTripleDes.Stream.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # TDEA-CMAC (3DES-CMAC, NIST SP 800-38B) on RISC-V -/

namespace VG.Artifacts.CmacTripleDes.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Cmac.tdesStreamInitApi.artifact RISCV64.target {
    code := Impl.CmacTripleDes.Stream.RISCV64.Fn.init
    verified := Proof.CmacTripleDes.Stream.RISCV64.Scrub.init_scrubbed },
  Spec.Cmac.tdesAbsorbApi.artifact RISCV64.target {
    code := Impl.CmacTripleDes.Stream.RISCV64.Fn.absorb
    verified := Proof.CmacTripleDes.Stream.RISCV64.Scrub.absorb_scrubbed },
  Spec.Cmac.tdesFinishApi.artifact RISCV64.target {
    code := Impl.CmacTripleDes.Stream.RISCV64.Fn.finish
    verified := Proof.CmacTripleDes.Stream.RISCV64.Scrub.finish_scrubbed }]

spec_apis artifacts

end VG.Artifacts.CmacTripleDes.RISCV64
