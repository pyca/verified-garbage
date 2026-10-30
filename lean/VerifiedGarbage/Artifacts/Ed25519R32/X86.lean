module

public import VerifiedGarbage.Proof.Ed25519.X86.Point32.Verified
import VerifiedGarbage.Proof.Ed25519.X86.Point32.Lit
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Ed25519's point additions and doubling, in radix `2^32`, on x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.Ed25519R32.X86

open VG.Spec.Ed25519.Point32 VG.Impl.Ed25519.X86.Point32 VG.Proof.Ed25519.X86.Point32

def artifacts : List Artifact := [
  addApi.artifact X86.target {
    code := addFn
    verified := addFn_verified },
  addAffineApi.artifact X86.target {
    code := affFn
    verified := affFn_verified },
  doubleApi.artifact X86.target {
    code := doubleFn
    verified := doubleFn_verified }]

end VG.Artifacts.Ed25519R32.X86
