module

public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Scrub
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # HMAC-SHA-384 (RFC 2104) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.HmacSha384.RISCV64

def artifacts : List Artifact := [
  Spec.Hmac.sha384I.initAnyKeyApi.artifact RISCV64.target Proof.Hmac.Stream.RISCV64.Scrub.sha384InitAnyKeyReg,
  Spec.Hmac.sha384I.finalizeApi.artifact RISCV64.target Proof.Hmac.Stream.RISCV64.Scrub.sha384FinalizeReg]

end VG.Artifacts.HmacSha384.RISCV64
