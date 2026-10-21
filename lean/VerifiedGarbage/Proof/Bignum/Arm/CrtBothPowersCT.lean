module

public import VerifiedGarbage.Proof.Bignum.Arm.WindowKernel
public import VerifiedGarbage.Proof.Bignum.Arm.CrtCheckedState
import VerifiedGarbage.Proof.Bignum.Arm.CrtPowerStageCT

/-! # Both private powers have identical traces for independent secret keys -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem crt_bothPowers_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} (kernel : WindowKernel := baselineWindowKernel) :
    RelCT isa (fun s t => CrtCheckedState g bs1 s ∧ CrtCheckedState g bs2 t ∧ s.sp = t.sp)
      (.seq ((CrtFn.powerWith kernel.code) 224 64 80) ((CrtFn.powerWith kernel.code) 228 72 88)) (fun _ _ => True) := by
  have first : RelCT isa (fun s t => CrtCheckedState g bs1 s ∧ CrtCheckedState g bs2 t ∧ s.sp = t.sp)
      ((CrtFn.powerWith kernel.code) 224 64 80) (fun _ _ => True) :=
    ((crt_powerStage_ct (kernel := kernel)) 1 3 (Or.inl ⟨rfl, rfl⟩)).mono
      (fun _ _ h => ⟨h.1.pSelection, h.2.1.pSelection, h.2.2⟩) (fun _ _ _ => trivial)
  exact crt_seq_ct first (fun s h => (crt_firstPower_qInput (kernel := kernel)) s h) (fun s h => (crt_firstPower_qInput (kernel := kernel)) s h)
    ((crt_powerStage_ct (kernel := kernel)) 2 4 (Or.inr ⟨rfl, rfl⟩))

end VG.Proof.Bignum.Arm
