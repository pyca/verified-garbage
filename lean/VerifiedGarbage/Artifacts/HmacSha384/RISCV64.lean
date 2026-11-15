module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha384
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # HMAC-SHA-384 (RFC 2104) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.HmacSha384.RISCV64

def artifacts : List Artifact := [
  Spec.Hmac.sha384I.initAnyKeyApi.artifact RISCV64.target {
    code := Proof.Hmac.Stream.RISCV64.Sha384.hash.init
    verified := Proof.Hmac.Stream.RISCV64.Sha384.init },
  Spec.Hmac.sha384I.finalizeApi.artifact RISCV64.target {
    code := Proof.Hmac.Stream.RISCV64.Sha384.hash.finalize
    verified := Proof.Hmac.Stream.RISCV64.Sha384.finalize }]

end VG.Artifacts.HmacSha384.RISCV64
