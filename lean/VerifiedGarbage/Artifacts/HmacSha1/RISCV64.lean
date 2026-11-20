module

public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Scrub
public import VerifiedGarbage.Impl.Hmac.Stream.RISCV64.Fn
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # HMAC-SHA-1 (RFC 2104) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.HmacSha1.RISCV64

def artifacts : List Artifact := [
  Spec.Hmac.sha1I.initAnyKeyApi.artifact RISCV64.target {
    code := Impl.Hmac.Stream.RISCV64.Fn.init Proof.Hmac.Stream.RISCV64.Sha1.hash
    verified := .scrubbed Proof.Hmac.Stream.RISCV64.Scrub.sha1_init_scrubbed },
  Spec.Hmac.sha1I.finalizeApi.artifact RISCV64.target {
    code := Impl.Hmac.Stream.RISCV64.Fn.finalize Proof.Hmac.Stream.RISCV64.Sha1.hash
    verified := .scrubbed Proof.Hmac.Stream.RISCV64.Scrub.sha1_finalize_scrubbed }]

end VG.Artifacts.HmacSha1.RISCV64
