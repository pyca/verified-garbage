module

public import VerifiedGarbage.Proof.MlDsa.AArch64.PkTr
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print

/-! # ML-DSA (FIPS 204) public-key hash `tr = H(pk, 64)` on AArch64 -/

@[expose] public section

namespace VG.Generic.Keccak.AArch64.MlDsaPkTr

def artifacts (v : Proof.Sha3.AArch64.Permutation) : List Artifact := [
  Spec.MlDsa.pkTr44Api.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    code := Impl.MlDsa.AArch64.PkTr.pkTrWith v.callee Spec.MlDsa.mlDsa44
    stack := 16
    verified := Proof.MlDsa.AArch64.PkTr.pkTr_verified v _ (.inl rfl) },
  Spec.MlDsa.pkTr65Api.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    code := Impl.MlDsa.AArch64.PkTr.pkTrWith v.callee Spec.MlDsa.mlDsa65
    stack := 16
    verified := Proof.MlDsa.AArch64.PkTr.pkTr_verified v _ (.inr (.inl rfl)) },
  Spec.MlDsa.pkTr87Api.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    code := Impl.MlDsa.AArch64.PkTr.pkTrWith v.callee Spec.MlDsa.mlDsa87
    stack := 16
    verified := Proof.MlDsa.AArch64.PkTr.pkTr_verified v _ (.inr (.inr rfl)) }]

end VG.Generic.Keccak.AArch64.MlDsaPkTr
