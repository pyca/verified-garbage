module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedSelected
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ML-DSA (FIPS 204) on AArch64: verifying messages -/

@[expose] public section

namespace VG.Generic.Keccak.AArch64.MlDsaVerifyMessageCached

open VG
open VG.Proof.MlDsa.AArch64.Verify.OptimizedSelected

def artifacts (v : Proof.Sha3.AArch64.Permutation) : List Artifact := [
  ((Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44")).artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    consts := selectedConsts v
    code := Impl.MlDsa.AArch64.Optimized.verifyMessageCached v.callee (Spec.MlDsa.verify44Api.name ++ v.callee.suffix)
      (selectedCode v Spec.MlDsa.mlDsa44) Spec.MlDsa.mlDsa44
    stack := 16
    verified := selected_cached_message_verified v (.inl rfl) (Spec.MlDsa.verify44Api.name ++ v.callee.suffix) },
  ((Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65")).artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    consts := selectedConsts v
    code := Impl.MlDsa.AArch64.Optimized.verifyMessageCached v.callee (Spec.MlDsa.verify65Api.name ++ v.callee.suffix)
      (selectedCode v Spec.MlDsa.mlDsa65) Spec.MlDsa.mlDsa65
    stack := 16
    verified := selected_cached_message_verified v (.inr (.inl rfl)) (Spec.MlDsa.verify65Api.name ++ v.callee.suffix) },
  ((Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87")).artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    consts := selectedConsts v
    code := Impl.MlDsa.AArch64.Optimized.verifyMessageCached v.callee (Spec.MlDsa.verify87Api.name ++ v.callee.suffix)
      (selectedCode v Spec.MlDsa.mlDsa87) Spec.MlDsa.mlDsa87
    stack := 16
    verified := selected_cached_message_verified v (.inr (.inr rfl)) (Spec.MlDsa.verify87Api.name ++ v.callee.suffix) }]

end VG.Generic.Keccak.AArch64.MlDsaVerifyMessageCached
