module

public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.MlDsa.AArch64.PreparedKey.Message
public import VerifiedGarbage.TCB.AArch64.Print

/-! # ML-DSA (FIPS 204) signing on AArch64 -/

@[expose] public section

namespace VG.Generic.Keccak.AArch64.MlDsaSign
open VG VG.Spec.MlDsa
open VG.Proof.MlDsa (signWithCacheName verifyWithCacheName preparedSignName preparedVerifyName)
open VG.Proof.MlDsa.AArch64.PreparedKey
open VG.Proof.MlDsa.AArch64.Sign

def entries (v : Proof.Sha3.AArch64.Permutation) (p : Params) (hp : Ok3 p)
    (module label : String) : List Artifact := [
  (signApi p module label).artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    code := signCode v p (signWithCacheName module ++ v.callee.suffix) false
    stack := 64
    verified := sign_entry_verified v hp _ false }]

def artifacts (v : Proof.Sha3.AArch64.Permutation) : List Artifact :=
  entries v mlDsa44 (.inl rfl) "mldsa44" "ML-DSA-44" ++
  entries v mlDsa65 (.inr (.inl rfl)) "mldsa65" "ML-DSA-65" ++
  entries v mlDsa87 (.inr (.inr rfl)) "mldsa87" "ML-DSA-87"

end VG.Generic.Keccak.AArch64.MlDsaSign
