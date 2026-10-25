module

public import VerifiedGarbage.Proof.Sha3.AArch64.MlDsaModes

public import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedSelected
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# ML-DSA (FIPS 204) on AArch64: verifying messages

A generic file (see `TCB/Emit.lean`): the artifacts it lists, which call
the SHA-3 sponge functions with an implementation `v` of the Keccak
permutation (`Variants/Keccak/AArch64/`), are emitted once for each
implementation, named with its suffix, and need its CPU features.
**Review note**: `sig` and `doc` are trusted, as they tie the Rust caller to
the contract; check them against the contract's `pre`/`post`. Each artifact
is made from its function's `Api` (in `Spec/MlDsa/CachedVerify.lean`, reviewed
with the contract), and this file adds only notes on the implementation. The
emitter adds the `# Safety` items that depend on the target
(`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

@[expose] public section

namespace VG.Generic.Keccak.AArch64.MlDsaVerifyMessageCached

open VG
open VG.Proof.MlDsa.AArch64.Verify.OptimizedSelected

/-- Notes on the implementation, the same for every parameter set. -/
def notes : List String :=
  ["The function saves its caller's `x28` and `x30` and its arguments in the last 1 KiB of `scratch`, \
    and uses no stack of its own; the functions it calls use the 16 bytes of stack below the stack \
    pointer. It reads the cached `tr = H(pk, 64)` and computes the message representative with the SHAKE256 sponge (`vg_keccak_absorb`, \
    `vg_keccak_pad`, `vg_keccak_squeeze`) in that 1 KiB, and calls the verification function on it, which \
    uses the rest of `scratch`."]

def artifactsOne (v : Proof.Sha3.AArch64.Permutation) : List Artifact := [
  ((Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44")).artifact AArch64.target {
    suffix := v.callee.mldsaSuffix
    features := Proof.Sha3.AArch64.mldsaFeatures v
    consts := selectedConsts v
    notes := notes
    code := Impl.MlDsa.AArch64.Optimized.verifyMessageCached v.callee (Spec.MlDsa.verify44Api.name ++ v.callee.mldsaSuffix)
      (selectedCode v Spec.MlDsa.mlDsa44) Spec.MlDsa.mlDsa44
    stack := 16
    verified := selected_cached_message_verified v (.inl rfl) (Spec.MlDsa.verify44Api.name ++ v.callee.mldsaSuffix) },
  ((Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65")).artifact AArch64.target {
    suffix := v.callee.mldsaSuffix
    features := Proof.Sha3.AArch64.mldsaFeatures v
    consts := selectedConsts v
    notes := notes
    code := Impl.MlDsa.AArch64.Optimized.verifyMessageCached v.callee (Spec.MlDsa.verify65Api.name ++ v.callee.mldsaSuffix)
      (selectedCode v Spec.MlDsa.mlDsa65) Spec.MlDsa.mlDsa65
    stack := 16
    verified := selected_cached_message_verified v (.inr (.inl rfl)) (Spec.MlDsa.verify65Api.name ++ v.callee.mldsaSuffix) },
  ((Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87")).artifact AArch64.target {
    suffix := v.callee.mldsaSuffix
    features := Proof.Sha3.AArch64.mldsaFeatures v
    consts := selectedConsts v
    notes := notes
    code := Impl.MlDsa.AArch64.Optimized.verifyMessageCached v.callee (Spec.MlDsa.verify87Api.name ++ v.callee.mldsaSuffix)
      (selectedCode v Spec.MlDsa.mlDsa87) Spec.MlDsa.mlDsa87
    stack := 16
    verified := selected_cached_message_verified v (.inr (.inr rfl)) (Spec.MlDsa.verify87Api.name ++ v.callee.mldsaSuffix) }]

def artifacts (v : Proof.Sha3.AArch64.Permutation) : List Artifact :=
  (Proof.Sha3.AArch64.mldsaModes v).flatMap artifactsOne

end VG.Generic.Keccak.AArch64.MlDsaVerifyMessageCached
