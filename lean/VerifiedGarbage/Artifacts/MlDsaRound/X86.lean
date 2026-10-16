module

import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.MlDsa.X86.Round.Power2Round
import VerifiedGarbage.Proof.MlDsa.X86.Round.Bits
public import VerifiedGarbage.Proof.MlDsa.X86.Round.NormLt
public import VerifiedGarbage.Proof.MlDsa.X86.Round.HintF
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# ML-DSA (FIPS 204) on x86: rounding and hints

The functions call no other one, and save their caller's registers in a
frame of 16 bytes below the return address (`stack := 16`).
`vg_mldsa_make_hint` and `vg_mldsa_use_hint` overwrite the argument `gamma2`
on the stack (which their contracts allow).
-/

@[expose] public section

namespace VG.Artifacts.MlDsaRound.X86

open VG.Proof.MlDsa.X86.Round

def artifacts : List Artifact := [
  Spec.MlDsa.power2RoundApi.artifact X86.target {
    code := Impl.MlDsa.X86.Round.power2Round
    stack := 16
    verified := power2Round_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  Spec.MlDsa.highBitsApi.artifact X86.target {
    code := Impl.MlDsa.X86.Round.highBits
    stack := 16
    verified := highBits_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  Spec.MlDsa.lowBitsApi.artifact X86.target {
    code := Impl.MlDsa.X86.Round.lowBits
    stack := 16
    verified := lowBits_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  Spec.MlDsa.normLtApi.artifact X86.target {
    code := Impl.MlDsa.X86.Round.normLt
    stack := 16
    verified := normLt_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  Spec.MlDsa.makeHintApi.artifact X86.target {
    code := Impl.MlDsa.X86.Round.makeHint
    stack := 16
    verified := makeHint_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  Spec.MlDsa.useHintApi.artifact X86.target {
    code := Impl.MlDsa.X86.Round.useHint
    stack := 16
    verified := useHint_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) }]

end VG.Artifacts.MlDsaRound.X86
