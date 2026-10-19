module

import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Verified
import Mathlib.Tactic.Conv
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.MlDsa.X86_64.Sign.Sign
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Inst
public import VerifiedGarbage.Spec.MlDsa.Contract

/-!
# ML-DSA (FIPS 204) on x86-64: signing

A generic file (see `TCB/Emit.lean`): the artifacts it lists, which call an
implementation `v` of the polynomial arithmetic (`vg_mldsa_ntt`, …), are
emitted once for each implementation (`Variants/MlDsaArith/X86_64/`), named
with its suffix (e.g. `vg_mldsa44_sign_avx2`), and need its CPU features.
-/

@[expose] public section

namespace VG.Generic.MlDsaArith.X86_64.MlDsaSign

open VG.Proof.MlDsa.X86_64 (ArithImpl)
open VG.Proof.MlDsa.X86_64.Sign (primsWith)

/-- Notes on the implementation, the same for every parameter set. -/
def notes : List String :=
  ["The function saves its caller's callee-saved registers in `scratch`; its calls use the 32 \
    bytes of stack below its return address.",
   "The signing loop runs at most 814 iterations (FIPS 204 Appendix C). Each iteration computes \
    every validity check and combines them without branching: the one branch on their result \
    is the only place an iteration's outcome affects timing."]

def artifacts (v : ArithImpl) : List Artifact := [
  Spec.MlDsa.sign44Api.artifact X86_64.target {
    suffix := v.code.sfx
    features := v.features
    notes := notes
    code := Impl.MlDsa.X86_64.Sign.sign (primsWith v.code) Spec.MlDsa.mlDsa44
    stack := 32
    verified := Proof.MlDsa.X86_64.Sign.sign_verified' v (.inl rfl)
    spSafe := Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inl rfl) },
  Spec.MlDsa.sign65Api.artifact X86_64.target {
    suffix := v.code.sfx
    features := v.features
    notes := notes
    code := Impl.MlDsa.X86_64.Sign.sign (primsWith v.code) Spec.MlDsa.mlDsa65
    stack := 32
    verified := Proof.MlDsa.X86_64.Sign.sign_verified' v (.inr (.inl rfl))
    spSafe := Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inr (.inl rfl)) },
  Spec.MlDsa.sign87Api.artifact X86_64.target {
    suffix := v.code.sfx
    features := v.features
    notes := notes
    code := Impl.MlDsa.X86_64.Sign.sign (primsWith v.code) Spec.MlDsa.mlDsa87
    stack := 32
    verified := Proof.MlDsa.X86_64.Sign.sign_verified' v (.inr (.inr rfl))
    spSafe := Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inr (.inr rfl)) }]

end VG.Generic.MlDsaArith.X86_64.MlDsaSign
