module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedSelected
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ML-DSA (FIPS 204) verification on AArch64 -/

@[expose] public section

namespace VG.Generic.Keccak.AArch64.MlDsaVerify
open VG.Proof.MlDsa.AArch64.Verify.OptimizedSelected

def artifacts (v : Proof.Sha3.AArch64.Permutation) : List Artifact := [
  Spec.MlDsa.verify44Api.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    consts := selectedConsts v
    code := selectedCode v Spec.MlDsa.mlDsa44
    stack := 16
    verified := selected_verify_verified v (.inl rfl) },
  Spec.MlDsa.verify65Api.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    consts := selectedConsts v
    code := selectedCode v Spec.MlDsa.mlDsa65
    stack := 16
    verified := selected_verify_verified v (.inr (.inl rfl)) },
  Spec.MlDsa.verify87Api.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    consts := selectedConsts v
    code := selectedCode v Spec.MlDsa.mlDsa87
    stack := 16
    verified := selected_verify_verified v (.inr (.inr rfl)) }]

end VG.Generic.Keccak.AArch64.MlDsaVerify
