module

import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Verified
import Mathlib.Tactic.Conv
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.MlDsa.X86_64.Sign.Sign
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Inst
public import VerifiedGarbage.Spec.MlDsa.Contract
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Verified
public import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.MlKem.X86_64.YLanes
import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Proof.MlDsa.Pack.Arith
public import VerifiedGarbage.Proof.MlDsa.Pack.Stream
public import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseCCT
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseDCT
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseKCT
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseOCT
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.SignCT
public import VerifiedGarbage.Proof.MlKem.X86_64.CompressEncode
public import VerifiedGarbage.Proof.MlKem.X86_64.DecodeDecompress
import VerifiedGarbage.Proof.MlDsa.Pack.Arith
import VerifiedGarbage.Proof.MlDsa.Pack.Stream
import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseCCT
import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseDCT
import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseKCT
import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseOCT
import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.SignCT
import VerifiedGarbage.Proof.MlKem.X86_64.CompressEncode
import VerifiedGarbage.Proof.MlKem.X86_64.DecodeDecompress

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
