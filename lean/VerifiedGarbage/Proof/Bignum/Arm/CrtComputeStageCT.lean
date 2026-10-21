module

public import VerifiedGarbage.Proof.Bignum.Arm.WindowKernel
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Proof.Bignum.Arm.CrtCheckedState
import VerifiedGarbage.Proof.Bignum.Arm.CrtComputeSelection
import VerifiedGarbage.Proof.Bignum.Arm.CrtBothPowersCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtCoefficientStageCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtFinishStageCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # The complete private computation has a secret-independent trace -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem crt_computeStage_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} (kernel : WindowKernel := baselineWindowKernel) :
    RelCT isa (fun s t => CrtCheckedState g bs1 s ∧ CrtCheckedState g bs2 t ∧ s.sp = t.sp)
      (CrtFn.computeWith kernel.code) (fun _ _ => True) := by
  have coefficient : RelCT isa (fun s t => CrtPoweredPair g bs1 s ∧ CrtPoweredPair g bs2 t ∧ s.sp = t.sp)
      CrtFn.coefficientPhase (fun _ _ => True) :=
    crt_coefficientStage_ct.mono (fun _ _ h => ⟨h.1.coefficientSelection, h.2.1.coefficientSelection, h.2.2⟩)
      (fun _ _ _ => trivial)
  exact (crt_seq_ct (crt_bothPowers_ct (kernel := kernel)) (fun s h => (crt_bothPowers_ready (kernel := kernel)) s h) (fun s h => (crt_bothPowers_ready (kernel := kernel)) s h)
    (crt_seq_ct coefficient (fun s h => crt_coefficientFinish_ready s h) (fun s h => crt_coefficientFinish_ready s h)
      crt_finishStage_ct)).assoc

end VG.Proof.Bignum.Arm
