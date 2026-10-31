module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha224
public import VerifiedGarbage.Proof.Framework.Registration

/-! # HMAC-SHA-224 (RFC 2104) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.HmacSha224.RISCV64

def artifacts : List Artifact := [
  Spec.Hmac.sha224I.initAnyKeyApi.artifact RISCV64.target {
    code := Proof.Hmac.Stream.RISCV64.Sha256Family.hash224.init
    stack := Proof.Hmac.Stream.RISCV64.Sha256Family.hash224.ibytes + Proof.Hmac.Stream.RISCV64.Sha256Family.hash224.F
    verified := Proof.Hmac.Stream.RISCV64.Sha224.init },
  Spec.Hmac.sha224I.finalizeApi.artifact RISCV64.target {
    code := Proof.Hmac.Stream.RISCV64.Sha256Family.hash224.finalize
    stack := Proof.Hmac.Stream.RISCV64.Sha256Family.hash224.fbytes + Proof.Hmac.Stream.RISCV64.Sha256Family.hash224.F
    verified := Proof.Hmac.Stream.RISCV64.Sha224.finalize }]

end VG.Artifacts.HmacSha224.RISCV64
