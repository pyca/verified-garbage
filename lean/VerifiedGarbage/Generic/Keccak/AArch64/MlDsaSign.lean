module

public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.MlDsa.AArch64.PreparedKey.Message

@[expose] public section

namespace VG.Generic.Keccak.AArch64.MlDsaSign
open VG VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.PreparedKey
open VG.Proof.MlDsa.AArch64.Sign

def entries (v : Proof.Sha3.AArch64.Permutation) (p : Params) (hp : Ok3 p)
    (module label : String) : List Artifact := [
  (signWithCacheApi p module label).artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    consts := pairedSignRootConsts
    code := Impl.MlDsa.AArch64.PreparedKey.Sign.withCache v.callee (primsWith v.callee) p
    stack := 48
    verified := withCache_verified v p hp },
  (signApi p module label).artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    consts := pairedSignRootConsts
    code := signCode v p ((signWithCacheApi p module label).name ++ v.callee.suffix) false
    stack := 64
    verified := sign_entry_verified v hp _ false },
  (preparedSignApi p module label).artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    consts := pairedSignRootConsts
    code := signCode v p ((signWithCacheApi p module label).name ++ v.callee.suffix) true
    stack := 64
    verified := sign_entry_verified v hp _ true }]

def artifacts (v : Proof.Sha3.AArch64.Permutation) : List Artifact :=
  entries v mlDsa44 (.inl rfl) "mldsa44" "ML-DSA-44" ++
  entries v mlDsa65 (.inr (.inl rfl)) "mldsa65" "ML-DSA-65" ++
  entries v mlDsa87 (.inr (.inr rfl)) "mldsa87" "ML-DSA-87"

end VG.Generic.Keccak.AArch64.MlDsaSign
