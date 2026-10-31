module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha512
public import VerifiedGarbage.Proof.Framework.Registration

/-! # HMAC-SHA-512 (RFC 2104) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.HmacSha512.RISCV64

def artifacts : List Artifact := [
  Spec.Hmac.sha512I.initAnyKeyApi.artifact RISCV64.target {
    code := Proof.Hmac.Stream.RISCV64.Sha512.hash.init
    stack := Proof.Hmac.Stream.RISCV64.Sha512.hash.ibytes + Proof.Hmac.Stream.RISCV64.Sha512.hash.F
    verified := Proof.Hmac.Stream.RISCV64.Sha512.init },
  Spec.Hmac.sha512I.finalizeApi.artifact RISCV64.target {
    code := Proof.Hmac.Stream.RISCV64.Sha512.hash.finalize
    stack := Proof.Hmac.Stream.RISCV64.Sha512.hash.fbytes + Proof.Hmac.Stream.RISCV64.Sha512.hash.F
    verified := Proof.Hmac.Stream.RISCV64.Sha512.finalize }]

end VG.Artifacts.HmacSha512.RISCV64
