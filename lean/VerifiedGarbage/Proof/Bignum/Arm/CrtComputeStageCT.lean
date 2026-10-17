module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtComputeSelection
public import VerifiedGarbage.Proof.Bignum.Arm.CrtBothPowersCT
public import VerifiedGarbage.Proof.Bignum.Arm.CrtCoefficientStageCT
public import VerifiedGarbage.Proof.Bignum.Arm.CrtFinishStageCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # The complete private computation has a secret-independent trace -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem crt_computeStage_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} :
    RelCT isa (fun s t => CrtCheckedState g bs1 s ∧ CrtCheckedState g bs2 t ∧ s.sp = t.sp)
      CrtFn.compute (fun _ _ => True) := by
  have coefficient : RelCT isa (fun s t => CrtPoweredPair g bs1 s ∧ CrtPoweredPair g bs2 t ∧ s.sp = t.sp)
      CrtFn.coefficientPhase (fun _ _ => True) :=
    crt_coefficientStage_ct.mono (fun _ _ h => ⟨h.1.coefficientSelection, h.2.1.coefficientSelection, h.2.2⟩)
      (fun _ _ _ => trivial)
  exact (crt_seq_ct crt_bothPowers_ct (fun s h => crt_bothPowers_ready s h) (fun s h => crt_bothPowers_ready s h)
    (crt_seq_ct coefficient (fun s h => crt_coefficientFinish_ready s h) (fun s h => crt_coefficientFinish_ready s h)
      crt_finishStage_ct)).assoc

end VG.Proof.Bignum.Arm
