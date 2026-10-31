module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha512_256
public import VerifiedGarbage.Proof.Framework.Registration

/-! # HMAC-SHA-512/256 (RFC 2104) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.HmacSha512_256.RISCV64

def artifacts : List Artifact := [
  Spec.Hmac.sha512_256I.initAnyKeyApi.artifact RISCV64.target {
    code := Proof.Hmac.Stream.RISCV64.Sha512_256.hash.init
    stack := Proof.Hmac.Stream.RISCV64.Sha512_256.hash.ibytes + Proof.Hmac.Stream.RISCV64.Sha512_256.hash.F
    verified := Proof.Hmac.Stream.RISCV64.Sha512_256.init },
  Spec.Hmac.sha512_256I.finalizeApi.artifact RISCV64.target {
    code := Proof.Hmac.Stream.RISCV64.Sha512_256.hash.finalize
    stack := Proof.Hmac.Stream.RISCV64.Sha512_256.hash.fbytes + Proof.Hmac.Stream.RISCV64.Sha512_256.hash.F
    verified := Proof.Hmac.Stream.RISCV64.Sha512_256.finalize }]

end VG.Artifacts.HmacSha512_256.RISCV64
