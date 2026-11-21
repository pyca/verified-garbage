module

public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Scrub
public import VerifiedGarbage.Impl.Hmac.Stream.RISCV64.Fn
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # HMAC-MD5 (RFC 2104) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.HmacMd5.RISCV64

def artifacts : List Artifact := [
  Spec.Hmac.md5I.initAnyKeyApi.artifact RISCV64.target {
    code := Impl.Hmac.Stream.RISCV64.Fn.init Proof.Hmac.Stream.RISCV64.Md5.hash
    verified := Proof.Hmac.Stream.RISCV64.Scrub.md5_init_scrubbed },
  Spec.Hmac.md5I.finalizeApi.artifact RISCV64.target {
    code := Impl.Hmac.Stream.RISCV64.Fn.finalize Proof.Hmac.Stream.RISCV64.Md5.hash
    verified := Proof.Hmac.Stream.RISCV64.Scrub.md5_finalize_scrubbed }]

end VG.Artifacts.HmacMd5.RISCV64
