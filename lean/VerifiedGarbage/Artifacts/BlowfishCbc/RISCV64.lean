module

public import VerifiedGarbage.Proof.Blowfish.RISCV64.Scrub
public import VerifiedGarbage.Impl.Blowfish.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Blowfish.RISCV64.ModesLit

/-! # Blowfish-CBC on RISC-V -/

@[expose] public section

namespace VG.Artifacts.BlowfishCbc.RISCV64

def artifacts : List Artifact := [
  Spec.Blowfish.cbcEncryptChainedApi.artifact RISCV64.target {
    code := Impl.Blowfish.RISCV64.Fn.cbcEncryptChained
    verified := Proof.Blowfish.RISCV64.Scrub.cbcEncryptChained_scrubbed },
  Spec.Blowfish.cbcDecryptChainedApi.artifact RISCV64.target {
    code := Impl.Blowfish.RISCV64.Fn.cbcDecryptChained
    verified := Proof.Blowfish.RISCV64.Scrub.cbcDecryptChained_scrubbed }]

end VG.Artifacts.BlowfishCbc.RISCV64
