module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Sha256.RISCV64.Shared
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha224
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # SHA-224 (FIPS 180-4) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Sha224.RISCV64

def artifacts : List Artifact := [
  Spec.Sha256.init224Api.artifact RISCV64.target {
    code := Impl.Sha256.RISCV64.Stream.init224
    verified := Proof.Sha256.RISCV64.Shared.init224 },
  Spec.Sha256.finalize224Api.artifact RISCV64.target {
    code := Impl.Sha256.RISCV64.Stream.finalize224
    stack := 144
    verified := Proof.Sha256.RISCV64.Shared.finalize224 },
  Spec.Sha256.digest224Api.artifact RISCV64.target {
    code := Impl.MdStream.RISCV64.Digest.digest Proof.Hmac.Stream.RISCV64.Sha256Family.hash224
    stack := Impl.MdStream.RISCV64.Digest.dbytes Proof.Hmac.Stream.RISCV64.Sha256Family.hash224 + Proof.Hmac.Stream.RISCV64.Sha256Family.hash224.F
    verified := Proof.Hmac.Stream.RISCV64.Sha224.digest }]

end VG.Artifacts.Sha224.RISCV64
