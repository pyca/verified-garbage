module

public import VerifiedGarbage.Proof.TripleDes.RISCV64.Scrub
public import VerifiedGarbage.Impl.TripleDes.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.TripleDes.RISCV64.ModesLit

/-! # Triple DES-CBC on RISC-V -/

@[expose] public section

namespace VG.Artifacts.TripleDesCbc.RISCV64

def artifacts : List Artifact := [
  Spec.TripleDes.cbcEncryptChainedApi.artifact RISCV64.target {
    code := Impl.TripleDes.RISCV64.Fn.cbcEncryptChained
    verified := Proof.TripleDes.RISCV64.Scrub.cbcEncryptChained_scrubbed },
  Spec.TripleDes.cbcDecryptChainedApi.artifact RISCV64.target {
    code := Impl.TripleDes.RISCV64.Fn.cbcDecryptChained
    verified := Proof.TripleDes.RISCV64.Scrub.cbcDecryptChained_scrubbed }]

end VG.Artifacts.TripleDesCbc.RISCV64
