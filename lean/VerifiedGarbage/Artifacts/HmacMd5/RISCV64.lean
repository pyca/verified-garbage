module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Hmac.Generic
import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Scrub
import VerifiedGarbage.Impl.Hmac.Stream.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # HMAC-MD5 (RFC 2104) on RISC-V -/

namespace VG.Artifacts.HmacMd5.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Hmac.md5I.initAnyKeyApi.artifact RISCV64.target {
    code := Impl.Hmac.Stream.RISCV64.Fn.init Proof.Hmac.Stream.RISCV64.Md5.hash
    verified := Proof.Hmac.Stream.RISCV64.Scrub.md5_init_scrubbed },
  Spec.Hmac.md5I.finalizeApi.artifact RISCV64.target {
    code := Impl.Hmac.Stream.RISCV64.Fn.finalize Proof.Hmac.Stream.RISCV64.Md5.hash
    verified := Proof.Hmac.Stream.RISCV64.Scrub.md5_finalize_scrubbed }]

spec_apis artifacts

end VG.Artifacts.HmacMd5.RISCV64
