module

public import VerifiedGarbage.Proof.Weierstrass.RISCV64.P256Field.Verified
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.P256Order.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Arithmetic modulo the curves' `p` and `n` on RISC-V -/

@[expose] public section

namespace VG.Artifacts.WeierstrassMont.RISCV64

open VG.Spec.Weierstrass.Mont VG.Impl.Weierstrass.RISCV64.P256Field VG.Proof.Weierstrass.RISCV64.P256Field

def artifacts : List Artifact := [
  p256p.mulApi.artifact RISCV64.target {
    code := mulFn
    verified := mul_verified },
  p256p.addApi.artifact RISCV64.target {
    code := addFn
    verified := add_verified },
  p256p.subApi.artifact RISCV64.target {
    code := subFn
    verified := sub_verified },
  p256n.mulApi.artifact RISCV64.target {
    code := VG.Impl.Weierstrass.RISCV64.P256Order.mulFn
    verified := VG.Proof.Weierstrass.RISCV64.P256Order.mul_verified },
  p256n.addApi.artifact RISCV64.target {
    code := VG.Impl.Weierstrass.RISCV64.P256Order.addFn
    verified := VG.Proof.Weierstrass.RISCV64.P256Order.add_verified },
  p256n.subApi.artifact RISCV64.target {
    code := VG.Impl.Weierstrass.RISCV64.P256Order.subFn
    verified := VG.Proof.Weierstrass.RISCV64.P256Order.sub_verified }]

end VG.Artifacts.WeierstrassMont.RISCV64
