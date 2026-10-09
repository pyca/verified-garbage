import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Inst
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedVerified

/-! # ML-DSA (FIPS 204) key generation on AArch64 -/

namespace VG.Generic.Keccak.AArch64.MlDsaKeyGen

/-- Notes on the implementation, the same for every parameter set. -/
def notes : List String :=
  ["The function saves its caller's `x24`–`x28` and `x30` in `scratch`, and uses no stack of its \
    own; the functions it calls use the 16 bytes of stack below the stack pointer.",
   "It samples every polynomial of `A` and of `s1` and `s2` whatever the samplers return, and \
    zeroes the polynomial of a sampler that fails rather than branching on it: its timing does not \
    depend on whether key generation fails."]

def legacyArtifacts (v : Proof.Sha3.AArch64.Permutation) : List Artifact := [
  { Spec.MlDsa.keyGen44Api with
    name := Spec.MlDsa.keyGen44Api.name ++ v.callee.suffix
    features := v.features
    target := AArch64.target
    doc := Spec.MlDsa.keyGen44Api.doc (notes := notes)
    code := Impl.MlDsa.AArch64.KeyGen.keyGen44With v.callee
    contract := Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa44 AArch64.abi 16
    stack := 16
    verified := Proof.MlDsa.AArch64.KeyGen.keyGen44_verifiedWith (keccak := v)
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.keyGen65Api with
    name := Spec.MlDsa.keyGen65Api.name ++ v.callee.suffix
    features := v.features
    target := AArch64.target
    doc := Spec.MlDsa.keyGen65Api.doc (notes := notes)
    code := Impl.MlDsa.AArch64.KeyGen.keyGen65With v.callee
    contract := Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa65 AArch64.abi 16
    stack := 16
    verified := Proof.MlDsa.AArch64.KeyGen.keyGen65_verifiedWith (keccak := v)
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.keyGen87Api with
    name := Spec.MlDsa.keyGen87Api.name ++ v.callee.suffix
    features := v.features
    target := AArch64.target
    doc := Spec.MlDsa.keyGen87Api.doc (notes := notes)
    code := Impl.MlDsa.AArch64.KeyGen.keyGen87With v.callee
    contract := Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa87 AArch64.abi 16
    stack := 16
    verified := Proof.MlDsa.AArch64.KeyGen.keyGen87_verifiedWith (keccak := v)
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

/-- SHA3 key generation uses hoisted matrix seeds, grouped secret sampling, and
positive transform arithmetic. The scalar fallback keeps its original code. -/
def optimizedArtifacts (v : Proof.Sha3.AArch64.Permutation) : List Artifact := [
  { Spec.MlDsa.keyGen44Api with
    name := Spec.MlDsa.keyGen44Api.name ++ v.callee.suffix
    features := v.features
    target := AArch64.target
    doc := Spec.MlDsa.keyGen44Api.doc (notes := notes)
    consts := Proof.MlDsa.AArch64.Sign.signRootConsts
    code := Impl.MlDsa.AArch64.KeyGen.Optimized.keyGenWith v.callee Spec.MlDsa.mlDsa44
    contract := Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa44
      (AArch64.abi.withConsts Proof.MlDsa.AArch64.Sign.signRootConsts) 16
    stack := 16
    verified := Proof.MlDsa.AArch64.KeyGen.Optimized.keyGen_verified v (.inl rfl)
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.keyGen65Api with
    name := Spec.MlDsa.keyGen65Api.name ++ v.callee.suffix
    features := v.features
    target := AArch64.target
    doc := Spec.MlDsa.keyGen65Api.doc (notes := notes)
    consts := Proof.MlDsa.AArch64.Sign.signRootConsts
    code := Impl.MlDsa.AArch64.KeyGen.Optimized.keyGenWith v.callee Spec.MlDsa.mlDsa65
    contract := Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa65
      (AArch64.abi.withConsts Proof.MlDsa.AArch64.Sign.signRootConsts) 16
    stack := 16
    verified := Proof.MlDsa.AArch64.KeyGen.Optimized.keyGen_verified v (.inr (.inl rfl))
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.keyGen87Api with
    name := Spec.MlDsa.keyGen87Api.name ++ v.callee.suffix
    features := v.features
    target := AArch64.target
    doc := Spec.MlDsa.keyGen87Api.doc (notes := notes)
    consts := Proof.MlDsa.AArch64.Sign.signRootConsts
    code := Impl.MlDsa.AArch64.KeyGen.Optimized.keyGenWith v.callee Spec.MlDsa.mlDsa87
    contract := Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa87
      (AArch64.abi.withConsts Proof.MlDsa.AArch64.Sign.signRootConsts) 16
    stack := 16
    verified := Proof.MlDsa.AArch64.KeyGen.Optimized.keyGen_verified v (.inr (.inr rfl))
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

def artifacts (v : Proof.Sha3.AArch64.Permutation) : List Artifact :=
  if v.callee.pairedSha3 then optimizedArtifacts v else legacyArtifacts v

end VG.Generic.Keccak.AArch64.MlDsaKeyGen
