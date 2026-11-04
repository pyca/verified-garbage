module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Sha1.RISCV64.Shared
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Sha1.RISCV64.Digest

/-! # SHA-1 (FIPS 180-4) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Sha1.RISCV64

def artifacts : List Artifact := [
  Spec.Sha1.initApi.artifact RISCV64.target {
    code := Impl.Sha1.RISCV64.Stream.init
    verified := Proof.Sha1.RISCV64.Shared.init },
  Spec.Sha1.updateApi.artifact RISCV64.target {
    code := Impl.Sha1.RISCV64.Stream.update
    stack := 144
    verified := Proof.Sha1.RISCV64.Shared.update },
  Spec.Sha1.finalizeApi.artifact RISCV64.target {
    code := Impl.Sha1.RISCV64.Stream.finalize
    stack := 144
    verified := Proof.Sha1.RISCV64.Shared.finalize },
  Spec.Sha1.digestApi.artifact RISCV64.target {
    code := Impl.MdStream.RISCV64.Digest.digest Proof.Hmac.Stream.RISCV64.Sha1.hash
    stack := Impl.MdStream.RISCV64.Digest.dbytes Proof.Hmac.Stream.RISCV64.Sha1.hash + Proof.Hmac.Stream.RISCV64.Sha1.hash.F
    verified := Proof.Sha1.RISCV64.Digest.verified }]

end VG.Artifacts.Sha1.RISCV64
