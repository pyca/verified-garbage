module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Md5
public import VerifiedGarbage.Proof.Framework.Registration

/-! # HMAC-MD5 (RFC 2104) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.HmacMd5.RISCV64

def artifacts : List Artifact := [
  Spec.Hmac.md5I.initAnyKeyApi.artifact RISCV64.target {
    code := Proof.Hmac.Stream.RISCV64.Md5.hash.init
    stack := Proof.Hmac.Stream.RISCV64.Md5.hash.ibytes + Proof.Hmac.Stream.RISCV64.Md5.hash.F
    verified := Proof.Hmac.Stream.RISCV64.Md5.init },
  Spec.Hmac.md5I.finalizeApi.artifact RISCV64.target {
    code := Proof.Hmac.Stream.RISCV64.Md5.hash.finalize
    stack := Proof.Hmac.Stream.RISCV64.Md5.hash.fbytes + Proof.Hmac.Stream.RISCV64.Md5.hash.F
    verified := Proof.Hmac.Stream.RISCV64.Md5.finalize }]

end VG.Artifacts.HmacMd5.RISCV64
