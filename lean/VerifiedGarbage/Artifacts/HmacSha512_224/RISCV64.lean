module

public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Scrub
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # HMAC-SHA-512/224 (RFC 2104) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.HmacSha512_224.RISCV64

def artifacts : List Artifact := [
  Spec.Hmac.sha512_224I.initAnyKeyApi.artifact RISCV64.target Proof.Hmac.Stream.RISCV64.Scrub.sha512_224InitAnyKeyReg,
  Spec.Hmac.sha512_224I.finalizeApi.artifact RISCV64.target Proof.Hmac.Stream.RISCV64.Scrub.sha512_224FinalizeReg]

end VG.Artifacts.HmacSha512_224.RISCV64
