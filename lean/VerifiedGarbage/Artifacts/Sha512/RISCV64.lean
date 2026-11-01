module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Sha512.RISCV64.Shared
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SHA-384, SHA-512, SHA-512/224 and SHA-512/256 (FIPS 180-4) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Sha512.RISCV64

def artifacts : List Artifact := [
  Spec.Sha512.init384Api.artifact RISCV64.target {
    code := Impl.Sha512.RISCV64.Stream.initWith Spec.Sha512.H0_384
    verified := Proof.Sha512.RISCV64.Shared.init384 },
  Spec.Sha512.init512Api.artifact RISCV64.target {
    code := Impl.Sha512.RISCV64.Stream.initWith Spec.Sha512.H0_512
    verified := Proof.Sha512.RISCV64.Shared.init512 },
  Spec.Sha512.init512_224Api.artifact RISCV64.target {
    code := Impl.Sha512.RISCV64.Stream.initWith Spec.Sha512.H0_512_224
    verified := Proof.Sha512.RISCV64.Shared.init512_224 },
  Spec.Sha512.init512_256Api.artifact RISCV64.target {
    code := Impl.Sha512.RISCV64.Stream.initWith Spec.Sha512.H0_512_256
    verified := Proof.Sha512.RISCV64.Shared.init512_256 },
  Spec.Sha512.updateApi.artifact RISCV64.target {
    code := Impl.Sha512.RISCV64.Stream.update
    stack := 208
    verified := Proof.Sha512.RISCV64.Shared.update },
  Spec.Sha512.finalizeApi.artifact RISCV64.target {
    code := Impl.Sha512.RISCV64.Stream.finalize
    stack := 208
    verified := Proof.Sha512.RISCV64.Shared.finalize },
  Spec.Sha512.finalize384Api.artifact RISCV64.target {
    code := Impl.Sha512.RISCV64.Stream.finalize384
    stack := 208
    verified := Proof.Sha512.RISCV64.Shared.finalize384 },
  Spec.Sha512.finalize512_256Api.artifact RISCV64.target {
    code := Impl.Sha512.RISCV64.Stream.finalize512_256
    stack := 208
    verified := Proof.Sha512.RISCV64.Shared.finalize512_256 },
  Spec.Sha512.finalize512_224Api.artifact RISCV64.target {
    code := Impl.Sha512.RISCV64.Stream.finalize512_224
    stack := 208
    verified := Proof.Sha512.RISCV64.Shared.finalize512_224 }]

end VG.Artifacts.Sha512.RISCV64
