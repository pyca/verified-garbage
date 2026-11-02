module

public import VerifiedGarbage.Proof.Bignum.RISCV64.PreVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # RSA (RFC 8017) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Rsa.RISCV64

def artifacts : List Artifact := [
  Spec.Rsa.publicPrecomputeApi.artifact RISCV64.target {
    code := Impl.Bignum.RISCV64.Precompute.precompute
    verified := Proof.Bignum.RISCV64.Pre.precompute_verified }]

end VG.Artifacts.Rsa.RISCV64
