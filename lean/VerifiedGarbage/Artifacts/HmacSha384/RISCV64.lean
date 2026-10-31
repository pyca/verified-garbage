module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha384
public import VerifiedGarbage.Proof.Framework.Registration

/-! # HMAC-SHA-384 (RFC 2104) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.HmacSha384.RISCV64

def artifacts : List Artifact := [
  Spec.Hmac.sha384I.initAnyKeyApi.artifact RISCV64.target {
    code := Proof.Hmac.Stream.RISCV64.Sha384.hash.init
    stack := Proof.Hmac.Stream.RISCV64.Sha384.hash.ibytes + Proof.Hmac.Stream.RISCV64.Sha384.hash.F
    verified := Proof.Hmac.Stream.RISCV64.Sha384.init },
  Spec.Hmac.sha384I.finalizeApi.artifact RISCV64.target {
    code := Proof.Hmac.Stream.RISCV64.Sha384.hash.finalize
    stack := Proof.Hmac.Stream.RISCV64.Sha384.hash.fbytes + Proof.Hmac.Stream.RISCV64.Sha384.hash.F
    verified := Proof.Hmac.Stream.RISCV64.Sha384.finalize }]

end VG.Artifacts.HmacSha384.RISCV64
