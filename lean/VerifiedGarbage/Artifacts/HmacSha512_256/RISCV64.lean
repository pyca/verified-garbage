module

public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Scrub
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # HMAC-SHA-512/256 (RFC 2104) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.HmacSha512_256.RISCV64

def artifacts : List Artifact := [
  Spec.Hmac.sha512_256I.initAnyKeyApi.artifact RISCV64.target Proof.Hmac.Stream.RISCV64.Scrub.sha512_256InitAnyKeyReg,
  Spec.Hmac.sha512_256I.finalizeApi.artifact RISCV64.target Proof.Hmac.Stream.RISCV64.Scrub.sha512_256FinalizeReg]

end VG.Artifacts.HmacSha512_256.RISCV64
