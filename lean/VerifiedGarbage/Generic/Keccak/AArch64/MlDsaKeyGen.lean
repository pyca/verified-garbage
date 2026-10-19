module

public import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Inst
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.OptimizedPrims
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Lit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Lit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Lit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRootsEntry
public import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Samp
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Lit
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentLit
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Depth

/-! # ML-DSA (FIPS 204) key generation on AArch64 -/

@[expose] public section

namespace VG.Generic.Keccak.AArch64.MlDsaKeyGen

/-- Notes on the implementation, the same for every parameter set. -/
def notes : List String :=
  ["The function saves its caller's `x24`–`x28` and `x30` in `scratch`, and uses no stack of its \
    own; the functions it calls use the 16 bytes of stack below the stack pointer.",
   "It samples every polynomial of `A` and of `s1` and `s2` whatever the samplers return, and \
    zeroes the polynomial of a sampler that fails rather than branching on it: its timing does not \
    depend on whether key generation fails."]

def legacyArtifacts (v : Proof.Sha3.AArch64.Permutation) : List Artifact := [
  Spec.MlDsa.keyGen44Api.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    notes := notes
    code := Impl.MlDsa.AArch64.KeyGen.keyGen44With v.callee
    stack := 16
    verified := Proof.MlDsa.AArch64.KeyGen.keyGen44_verifiedWith (keccak := v) },
  Spec.MlDsa.keyGen65Api.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    notes := notes
    code := Impl.MlDsa.AArch64.KeyGen.keyGen65With v.callee
    stack := 16
    verified := Proof.MlDsa.AArch64.KeyGen.keyGen65_verifiedWith (keccak := v) },
  Spec.MlDsa.keyGen87Api.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    notes := notes
    code := Impl.MlDsa.AArch64.KeyGen.keyGen87With v.callee
    stack := 16
    verified := Proof.MlDsa.AArch64.KeyGen.keyGen87_verifiedWith (keccak := v) }]

/-- SHA3 key generation uses hoisted matrix seeds, grouped secret sampling, and
positive transform arithmetic. The scalar fallback shares its grouped secret
sampling (`Optimized.secretsWith`), with the four-way samplers of its own
permutation. -/
def optimizedArtifacts (v : Proof.Sha3.AArch64.Permutation) : List Artifact := [
  Spec.MlDsa.keyGen44Api.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    notes := notes
    consts := Proof.MlDsa.AArch64.Sign.signRootConsts
    code := Impl.MlDsa.AArch64.KeyGen.Optimized.keyGenWith v.callee Spec.MlDsa.mlDsa44
    stack := 16
    verified := Proof.MlDsa.AArch64.KeyGen.Optimized.keyGen_verified v (.inl rfl) },
  Spec.MlDsa.keyGen65Api.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    notes := notes
    consts := Proof.MlDsa.AArch64.Sign.signRootConsts
    code := Impl.MlDsa.AArch64.KeyGen.Optimized.keyGenWith v.callee Spec.MlDsa.mlDsa65
    stack := 16
    verified := Proof.MlDsa.AArch64.KeyGen.Optimized.keyGen_verified v (.inr (.inl rfl)) },
  Spec.MlDsa.keyGen87Api.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    notes := notes
    consts := Proof.MlDsa.AArch64.Sign.signRootConsts
    code := Impl.MlDsa.AArch64.KeyGen.Optimized.keyGenWith v.callee Spec.MlDsa.mlDsa87
    stack := 16
    verified := Proof.MlDsa.AArch64.KeyGen.Optimized.keyGen_verified v (.inr (.inr rfl)) }]

def artifacts (v : Proof.Sha3.AArch64.Permutation) : List Artifact :=
  if v.callee.pairedSha3 then optimizedArtifacts v else legacyArtifacts v

end VG.Generic.Keccak.AArch64.MlDsaKeyGen
