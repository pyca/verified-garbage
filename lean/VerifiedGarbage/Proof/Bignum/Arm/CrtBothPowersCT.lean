module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtCheckedState
public import VerifiedGarbage.Proof.Bignum.Arm.CrtPowerStageCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Both private powers have identical traces for independent secret keys -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem crt_bothPowers_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} :
    RelCT isa (fun s t => CrtCheckedState g bs1 s ∧ CrtCheckedState g bs2 t ∧ s.sp = t.sp)
      (.seq (CrtFn.power 224 64 80) (CrtFn.power 228 72 88)) (fun _ _ => True) := by
  have first : RelCT isa (fun s t => CrtCheckedState g bs1 s ∧ CrtCheckedState g bs2 t ∧ s.sp = t.sp)
      (CrtFn.power 224 64 80) (fun _ _ => True) :=
    (crt_powerStage_ct 1 3 (Or.inl ⟨rfl, rfl⟩)).mono
      (fun _ _ h => ⟨h.1.pSelection, h.2.1.pSelection, h.2.2⟩) (fun _ _ _ => trivial)
  exact crt_seq_ct first (fun s h => crt_firstPower_qInput s h) (fun s h => crt_firstPower_qInput s h)
    (crt_powerStage_ct 2 4 (Or.inr ⟨rfl, rfl⟩))

end VG.Proof.Bignum.Arm
