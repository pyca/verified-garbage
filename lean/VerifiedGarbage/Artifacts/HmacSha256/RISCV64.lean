module

public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Scrub
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # HMAC-SHA-256 (RFC 2104) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.HmacSha256.RISCV64

def artifacts : List Artifact := [
  Spec.Hmac.sha256I.initAnyKeyApi.artifact RISCV64.target Proof.Hmac.Stream.RISCV64.Scrub.sha256InitAnyKeyReg,
  Spec.Hmac.sha256I.finalizeApi.artifact RISCV64.target Proof.Hmac.Stream.RISCV64.Scrub.sha256FinalizeReg]

end VG.Artifacts.HmacSha256.RISCV64
