module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedSelected
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Depth

/-! # ML-DSA (FIPS 204) signing on AArch64 -/

@[expose] public section

namespace VG.Generic.Keccak.AArch64.MlDsaSign

open VG
open VG.Proof.MlDsa.AArch64.Sign (primsWith)

/-- Notes on the implementation, the same for every parameter set. -/
def notes : List String :=
  ["The function saves its caller's callee-saved registers and its return address in `scratch`; \
    the frames of its calls use the 16 bytes of stack below the stack pointer.",
   "The signing loop runs at most 814 iterations (FIPS 204 Appendix C). Each iteration computes \
    every validity check and combines them without branching: the one branch on their result \
    is the only place an iteration's outcome affects timing."]

def artifacts (v : Proof.Sha3.AArch64.Permutation) : List Artifact := [
  Spec.MlDsa.sign44Api.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    notes := notes
    consts := Proof.MlDsa.AArch64.Sign.pairedSignRootConsts
    code := Impl.MlDsa.AArch64.Sign.Optimized.signWith v.callee (primsWith v.callee) Spec.MlDsa.mlDsa44
      (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks Spec.MlDsa.mlDsa44)
    stack := 16
    verified := Proof.MlDsa.AArch64.Sign.pairedSign_verified v (.inl rfl) },
  Spec.MlDsa.sign65Api.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    notes := notes
    consts := Proof.MlDsa.AArch64.Sign.pairedSignRootConsts
    code := Proof.MlDsa.AArch64.Sign.CachedSelected.code v Spec.MlDsa.mlDsa65
    stack := 16
    verified := Proof.MlDsa.AArch64.Sign.CachedSelected.verified v (.inl rfl) },
  Spec.MlDsa.sign87Api.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    notes := notes
    consts := Proof.MlDsa.AArch64.Sign.pairedSignRootConsts
    code := Proof.MlDsa.AArch64.Sign.CachedSelected.code v Spec.MlDsa.mlDsa87
    stack := 16
    verified := Proof.MlDsa.AArch64.Sign.CachedSelected.verified v (.inr rfl) }]

end VG.Generic.Keccak.AArch64.MlDsaSign
