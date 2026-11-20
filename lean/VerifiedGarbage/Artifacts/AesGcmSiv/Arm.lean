module

public import VerifiedGarbage.Proof.Gcm.Arm.Law
public import VerifiedGarbage.Proof.AesGcmSiv.Arm.Verified
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # AES-GCM-SIV (RFC 8452) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.AesGcmSiv.Arm

def artifacts : List Artifact := [
  Spec.GcmSiv.sealApi.artifact Arm.target {
    code := Impl.AesGcmSiv.Arm.Fn.«seal»
    verified := .scrubbed Proof.AesGcmSiv.Arm.Fn.«seal» },
  Spec.GcmSiv.openApi.artifact Arm.target {
    code := Impl.AesGcmSiv.Arm.Fn.«open»
    verified := .scrubbed Proof.AesGcmSiv.Arm.Fn.«open» }]

end VG.Artifacts.AesGcmSiv.Arm
