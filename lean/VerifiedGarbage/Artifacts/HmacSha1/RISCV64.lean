module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha1
public import VerifiedGarbage.Proof.Framework.Registration

/-! # HMAC-SHA-1 (RFC 2104) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.HmacSha1.RISCV64

def artifacts : List Artifact := [
  Spec.Hmac.sha1I.initAnyKeyApi.artifact RISCV64.target {
    code := Proof.Hmac.Stream.RISCV64.Sha1.hash.init
    stack := Proof.Hmac.Stream.RISCV64.Sha1.hash.ibytes + Proof.Hmac.Stream.RISCV64.Sha1.hash.F
    verified := Proof.Hmac.Stream.RISCV64.Sha1.init },
  Spec.Hmac.sha1I.finalizeApi.artifact RISCV64.target {
    code := Proof.Hmac.Stream.RISCV64.Sha1.hash.finalize
    stack := Proof.Hmac.Stream.RISCV64.Sha1.hash.fbytes + Proof.Hmac.Stream.RISCV64.Sha1.hash.F
    verified := Proof.Hmac.Stream.RISCV64.Sha1.finalize }]

end VG.Artifacts.HmacSha1.RISCV64
