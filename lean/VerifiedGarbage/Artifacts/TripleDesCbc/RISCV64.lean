module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.TripleDes.Cbc
import VerifiedGarbage.Proof.TripleDes.RISCV64.Scrub
import VerifiedGarbage.Impl.TripleDes.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.TripleDes.RISCV64.ModesLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Triple DES-CBC on RISC-V -/

namespace VG.Artifacts.TripleDesCbc.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.TripleDes.cbcEncryptChainedApi.artifact RISCV64.target {
    code := Impl.TripleDes.RISCV64.Fn.cbcEncryptChained
    verified := Proof.TripleDes.RISCV64.Scrub.cbcEncryptChained_scrubbed },
  Spec.TripleDes.cbcDecryptChainedApi.artifact RISCV64.target {
    code := Impl.TripleDes.RISCV64.Fn.cbcDecryptChained
    verified := Proof.TripleDes.RISCV64.Scrub.cbcDecryptChained_scrubbed }]

spec_apis artifacts

end VG.Artifacts.TripleDesCbc.RISCV64
