module

import VerifiedGarbage.Proof.MlKem.AArch64.KeyGen
public import VerifiedGarbage.Proof.MlKem.AArch64.Encaps
import VerifiedGarbage.Proof.MlKem.AArch64.Decaps
public import VerifiedGarbage.Proof.MlKem1024.AArch64.KeyGen
public import VerifiedGarbage.Proof.MlKem1024.AArch64.Encaps
public import VerifiedGarbage.Proof.MlKem1024.AArch64.Decaps
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Verified
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.KeyGenFinal
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.EncapsVerified
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.DecapsVerified
import Mathlib.Tactic.Conv
import Mathlib.Tactic.SplitIfs

/-! `keygen`, `encaps` and `decaps` of ML-KEM-768 and ML-KEM-1024, for each
Keccak implementation: the same code and proofs, for each parameter set. -/

@[expose] public section

namespace VG.Generic.Keccak.AArch64.MlKem

def legacyArtifacts (v : Proof.Sha3.AArch64.Permutation) : List Artifact := [
  { Spec.MlKem.keyGenApi with
    name := Spec.MlKem.keyGenApi.name ++ v.callee.suffix
    features := v.features
    target := AArch64.target
    doc := Spec.MlKem.keyGenApi.doc
    code := Impl.MlKem.AArch64.keyGenWith v.callee
    contract := Spec.MlKem.keyGenContract AArch64.abi 16
    stack := 16
    verified := Proof.MlKem.AArch64.KeyGen.keyGen_verifiedWith (keccak := v)
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlKem.encapsApi with
    name := Spec.MlKem.encapsApi.name ++ v.callee.suffix
    features := v.features
    target := AArch64.target
    doc := Spec.MlKem.encapsApi.doc
    code := Impl.MlKem.AArch64.encapsWith v.callee
    contract := Spec.MlKem.encapsContract AArch64.abi 16
    stack := 16
    verified := Proof.MlKem.AArch64.Encaps.encaps_verifiedWith (keccak := v)
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlKem.decapsApi with
    name := Spec.MlKem.decapsApi.name ++ v.callee.suffix
    features := v.features
    target := AArch64.target
    doc := Spec.MlKem.decapsApi.doc
    code := Impl.MlKem.AArch64.decapsWith v.callee
    contract := Spec.MlKem.decapsContract AArch64.abi 16
    stack := 16
    verified := Proof.MlKem.AArch64.Decaps.decaps_verifiedWith (keccak := v)
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlKem1024.keyGenApi with
    name := Spec.MlKem1024.keyGenApi.name ++ v.callee.suffix
    features := v.features
    target := AArch64.target
    doc := Spec.MlKem1024.keyGenApi.doc
    code := Impl.MlKem1024.AArch64.keyGenWith v.callee
    contract := Spec.MlKem1024.keyGenContract AArch64.abi 16
    stack := 16
    verified := Proof.MlKem1024.AArch64.KeyGen.keyGen_verifiedWith (keccak := v)
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlKem1024.encapsApi with
    name := Spec.MlKem1024.encapsApi.name ++ v.callee.suffix
    features := v.features
    target := AArch64.target
    doc := Spec.MlKem1024.encapsApi.doc
    code := Impl.MlKem1024.AArch64.encapsWith v.callee
    contract := Spec.MlKem1024.encapsContract AArch64.abi 16
    stack := 16
    verified := Proof.MlKem1024.AArch64.Encaps.encaps_verifiedWith (keccak := v)
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlKem1024.decapsApi with
    name := Spec.MlKem1024.decapsApi.name ++ v.callee.suffix
    features := v.features
    target := AArch64.target
    doc := Spec.MlKem1024.decapsApi.doc
    code := Impl.MlKem1024.AArch64.decapsWith v.callee
    contract := Spec.MlKem1024.decapsContract AArch64.abi 16
    stack := 16
    verified := Proof.MlKem1024.AArch64.Decaps.decaps_verifiedWith (keccak := v)
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

/-- Paired sampling and fused arithmetic for the hardware SHA3 backend. -/
def optimizedArtifacts : List Artifact := [
  { Spec.MlKem.keyGenApi with
    name := Spec.MlKem.keyGenApi.name ++ "_paired_sha3"
    features := Proof.Sha3.AArch64.Sha3.backend.features
    target := AArch64.target
    doc := Spec.MlKem.keyGenApi.doc
    consts := Proof.MlKem.AArch64.Optimized.constants
    code := Impl.MlKem.AArch64.FixedHashCallers.keyGenUsing Proof.MlKem.AArch64.FixedHash.fixedHash Impl.MlKem.AArch64.lay768
    contract := Proof.MlKem.AArch64.Optimized.keyGen768Contract
    stack := 16
    verified := Proof.MlKem.AArch64.FixedHash.keyGen768_final
    ofSig := by exact ⟨_, _, _, by unfold Proof.MlKem.AArch64.Optimized.keyGen768Contract Spec.MlKem.keyGenContract; rfl⟩
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlKem.encapsApi with
    name := Spec.MlKem.encapsApi.name ++ "_paired_sha3"
    features := Proof.Sha3.AArch64.Sha3.backend.features
    target := AArch64.target
    doc := Spec.MlKem.encapsApi.doc
    consts := Proof.MlKem.AArch64.Optimized.constants
    code := Impl.MlKem.AArch64.Optimized.encapsUsing (Impl.MlKem.AArch64.FixedHashCallers.enAUsing Proof.MlKem.AArch64.FixedHash.fixedHash Impl.MlKem.AArch64.lay768) Proof.MlKem.AArch64.FixedHash.prf Impl.MlKem.AArch64.lay768
    contract := Proof.MlKem.AArch64.Optimized.encaps768Contract
    stack := 16
    verified := Proof.MlKem.AArch64.FixedHash.encaps768_verified
    ofSig := by exact ⟨_, _, _, by unfold Proof.MlKem.AArch64.Optimized.encaps768Contract Spec.MlKem.encapsContract; rfl⟩
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlKem.decapsApi with
    name := Spec.MlKem.decapsApi.name ++ "_paired_sha3"
    features := Proof.Sha3.AArch64.Sha3.backend.features
    target := AArch64.target
    doc := Spec.MlKem.decapsApi.doc
    consts := Proof.MlKem.AArch64.Optimized.constants
    code := Impl.MlKem.AArch64.FixedHashDecaps.decapsUsing Proof.MlKem.AArch64.FixedHash.fixedHash Proof.MlKem.AArch64.FixedHash.prf Impl.MlKem.AArch64.lay768
    contract := Proof.MlKem.AArch64.Optimized.decaps768Contract
    stack := 16
    verified := Proof.MlKem.AArch64.FixedHash.decaps768_verified
    ofSig := by exact ⟨_, _, _, by unfold Proof.MlKem.AArch64.Optimized.decaps768Contract Spec.MlKem.decapsContract; rfl⟩
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlKem1024.keyGenApi with
    name := Spec.MlKem1024.keyGenApi.name ++ "_paired_sha3"
    features := Proof.Sha3.AArch64.Sha3.backend.features
    target := AArch64.target
    doc := Spec.MlKem1024.keyGenApi.doc
    consts := Proof.MlKem.AArch64.Optimized.constants
    code := Impl.MlKem.AArch64.FixedHashCallers.keyGenUsing Proof.MlKem.AArch64.FixedHash.fixedHash Impl.MlKem1024.AArch64.lay1024
    contract := Proof.MlKem.AArch64.Optimized.keyGen1024Contract
    stack := 16
    verified := Proof.MlKem.AArch64.FixedHash.keyGen1024_final
    ofSig := by exact ⟨_, _, _, by unfold Proof.MlKem.AArch64.Optimized.keyGen1024Contract Spec.MlKem1024.keyGenContract; rfl⟩
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlKem1024.encapsApi with
    name := Spec.MlKem1024.encapsApi.name ++ "_paired_sha3"
    features := Proof.Sha3.AArch64.Sha3.backend.features
    target := AArch64.target
    doc := Spec.MlKem1024.encapsApi.doc
    consts := Proof.MlKem.AArch64.Optimized.constants
    code := Impl.MlKem.AArch64.Optimized.encapsUsing (Impl.MlKem.AArch64.FixedHashCallers.enAUsing Proof.MlKem.AArch64.FixedHash.fixedHash Impl.MlKem1024.AArch64.lay1024) Proof.MlKem.AArch64.FixedHash.prf Impl.MlKem1024.AArch64.lay1024
    contract := Proof.MlKem.AArch64.Optimized.encaps1024Contract
    stack := 16
    verified := Proof.MlKem.AArch64.FixedHash.encaps1024_verified
    ofSig := by exact ⟨_, _, _, by unfold Proof.MlKem.AArch64.Optimized.encaps1024Contract Spec.MlKem1024.encapsContract; rfl⟩
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlKem1024.decapsApi with
    name := Spec.MlKem1024.decapsApi.name ++ "_paired_sha3"
    features := Proof.Sha3.AArch64.Sha3.backend.features
    target := AArch64.target
    doc := Spec.MlKem1024.decapsApi.doc
    consts := Proof.MlKem.AArch64.Optimized.constants
    code := Impl.MlKem.AArch64.FixedHashDecaps.decapsUsing Proof.MlKem.AArch64.FixedHash.fixedHash Proof.MlKem.AArch64.FixedHash.prf Impl.MlKem1024.AArch64.lay1024
    contract := Proof.MlKem.AArch64.Optimized.decaps1024Contract
    stack := 16
    verified := Proof.MlKem.AArch64.FixedHash.decaps1024_verified
    ofSig := by exact ⟨_, _, _, by unfold Proof.MlKem.AArch64.Optimized.decaps1024Contract Spec.MlKem1024.decapsContract; rfl⟩
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

def artifacts (v : Proof.Sha3.AArch64.Permutation) : List Artifact :=
  legacyArtifacts v ++ if v.callee.pairedSha3 then optimizedArtifacts else []

end VG.Generic.Keccak.AArch64.MlKem
