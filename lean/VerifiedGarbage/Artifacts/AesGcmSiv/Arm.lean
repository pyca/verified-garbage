module

public import VerifiedGarbage.Proof.AesGcmSiv.Arm.Verified
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset
public import VerifiedGarbage.Proof.Framework.Registration

/-! # AES-GCM-SIV (RFC 8452) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.AesGcmSiv.Arm

open VG.Proof.AesGcmSiv.Arm

def artifacts : List Artifact := [
  Spec.GcmSiv.sealApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 3792 4 Impl.AesGcmSiv.Arm.«seal»
    stack := 3800
    verified := seal_framed },
  Spec.GcmSiv.openApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratch 3792 4 Impl.AesGcmSiv.Arm.«open»
    stack := 3800
    verified := open_framed }]

end VG.Artifacts.AesGcmSiv.Arm
