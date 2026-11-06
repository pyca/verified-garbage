module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Sha3.RISCV64.Instances
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # SHA-3 and SHAKE (FIPS 202) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Sha3.RISCV64

def artifacts : List Artifact := [
  Spec.Sha3.updateSha3_224Api.artifact RISCV64.target {
    code := Impl.Sha3.RISCV64.Instances.update Spec.Sha3.hashSha3_224.rate
    stack := 608
    verified := Proof.Sha3.RISCV64.Instances.update_sha3_224 },
  Spec.Sha3.finalizeSha3_224Api.artifact RISCV64.target {
    code := Impl.Sha3.RISCV64.Instances.finalize Spec.Sha3.hashSha3_224.rate Spec.Sha3.hashSha3_224.len
    stack := 1168 + 32
    verified := Proof.Sha3.RISCV64.Instances.finalize_sha3_224 },
  Spec.Sha3.updateSha3_256Api.artifact RISCV64.target {
    code := Impl.Sha3.RISCV64.Instances.update Spec.Sha3.hashSha3_256.rate
    stack := 608
    verified := Proof.Sha3.RISCV64.Instances.update_sha3_256 },
  Spec.Sha3.finalizeSha3_256Api.artifact RISCV64.target {
    code := Impl.Sha3.RISCV64.Instances.finalize Spec.Sha3.hashSha3_256.rate Spec.Sha3.hashSha3_256.len
    stack := 1168 + 32
    verified := Proof.Sha3.RISCV64.Instances.finalize_sha3_256 },
  Spec.Sha3.updateSha3_384Api.artifact RISCV64.target {
    code := Impl.Sha3.RISCV64.Instances.update Spec.Sha3.hashSha3_384.rate
    stack := 608
    verified := Proof.Sha3.RISCV64.Instances.update_sha3_384 },
  Spec.Sha3.finalizeSha3_384Api.artifact RISCV64.target {
    code := Impl.Sha3.RISCV64.Instances.finalize Spec.Sha3.hashSha3_384.rate Spec.Sha3.hashSha3_384.len
    stack := 1168 + 32
    verified := Proof.Sha3.RISCV64.Instances.finalize_sha3_384 },
  Spec.Sha3.updateSha3_512Api.artifact RISCV64.target {
    code := Impl.Sha3.RISCV64.Instances.update Spec.Sha3.hashSha3_512.rate
    stack := 608
    verified := Proof.Sha3.RISCV64.Instances.update_sha3_512 },
  Spec.Sha3.finalizeSha3_512Api.artifact RISCV64.target {
    code := Impl.Sha3.RISCV64.Instances.finalize Spec.Sha3.hashSha3_512.rate Spec.Sha3.hashSha3_512.len
    stack := 1168 + 32
    verified := Proof.Sha3.RISCV64.Instances.finalize_sha3_512 },
  Spec.Sha3.updateShake128Api.artifact RISCV64.target {
    code := Impl.Sha3.RISCV64.Instances.update Spec.Sha3.xofShake128.rate
    stack := 608
    verified := Proof.Sha3.RISCV64.Instances.update_shake128 },
  Spec.Sha3.finalizeShake128Api.artifact RISCV64.target {
    code := Impl.Sha3.RISCV64.Instances.xofFinalize Spec.Sha3.xofShake128.rate
    stack := 1136
    verified := Proof.Sha3.RISCV64.Instances.finalize_shake128 },
  Spec.Sha3.squeezeShake128Api.artifact RISCV64.target {
    code := Impl.Sha3.RISCV64.Instances.xofSqueeze Spec.Sha3.xofShake128.rate
    stack := 1168
    verified := Proof.Sha3.RISCV64.Instances.squeeze_shake128 },
  Spec.Sha3.updateShake256Api.artifact RISCV64.target {
    code := Impl.Sha3.RISCV64.Instances.update Spec.Sha3.xofShake256.rate
    stack := 608
    verified := Proof.Sha3.RISCV64.Instances.update_shake256 },
  Spec.Sha3.finalizeShake256Api.artifact RISCV64.target {
    code := Impl.Sha3.RISCV64.Instances.xofFinalize Spec.Sha3.xofShake256.rate
    stack := 1136
    verified := Proof.Sha3.RISCV64.Instances.finalize_shake256 },
  Spec.Sha3.squeezeShake256Api.artifact RISCV64.target {
    code := Impl.Sha3.RISCV64.Instances.xofSqueeze Spec.Sha3.xofShake256.rate
    stack := 1168
    verified := Proof.Sha3.RISCV64.Instances.squeeze_shake256 }]

end VG.Artifacts.Sha3.RISCV64
