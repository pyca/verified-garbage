module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Sha3.RISCV64.Permute
public import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SHA-3 and SHAKE (FIPS 202) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Sha3.RISCV64

def artifacts : List Artifact := [
  Spec.Sha3.absorbApi.artifact RISCV64.target {
    code := Impl.Sha3.RISCV64.Stream.absorb
    stack := 1168
    verified := Proof.Sha3.RISCV64.Stream.absorb_verified },
  Spec.Sha3.padApi.artifact RISCV64.target {
    code := Impl.Sha3.RISCV64.Stream.pad
    stack := 1136
    verified := Proof.Sha3.RISCV64.Stream.pad_verified },
  Spec.Sha3.squeezeApi.artifact RISCV64.target {
    code := Impl.Sha3.RISCV64.Stream.squeeze
    stack := 1168
    verified := Proof.Sha3.RISCV64.Stream.squeeze_verified }]

end VG.Artifacts.Sha3.RISCV64
