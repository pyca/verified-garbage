module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Ed25519.RISCV64.FieldVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Products and powers in curve25519's field, in radix `2^32`, on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Gf25519R32.RISCV64

open VG.Spec.X25519.Field32 VG.Impl.Ed25519.RISCV64 VG.Proof.Ed25519.RISCV64

def artifacts : List Artifact := [
  mulApi.artifact RISCV64.target {
    code := mulFn
    verified := mulFn_verified },
  pow250Api.artifact RISCV64.target {
    code := pow250Fn
    verified := pow250Fn_verified }]

end VG.Artifacts.Gf25519R32.RISCV64
