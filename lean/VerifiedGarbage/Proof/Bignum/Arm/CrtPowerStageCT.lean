module

public import VerifiedGarbage.Proof.Bignum.Arm.WindowKernel

public import VerifiedGarbage.Proof.Bignum.Arm.CrtPowerSelection
public import VerifiedGarbage.Impl.Bignum.Arm.CrtFn
import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowPowerCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtWorkspaceCallCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Layout

/-! # A selected factor power hides factor, exponent, input, and acceptance -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt

theorem crt_powerStage_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} {child : BitVec 32} {slot : Nat}
    (j i : Fin 6) (pair : (j = 1 ∧ i = 3) ∨ (j = 2 ∧ i = 4)) (kernel : WindowKernel := baselineWindowKernel) :
    RelCT isa (fun s t => CrtPowerSelection g bs1 child slot j s ∧ CrtPowerSelection g bs2 child slot j t ∧
      s.sp = t.sp) ((CrtFn.powerWith kernel.code) slot (56 + 8 * j.val) (56 + 8 * i.val)) (fun _ _ => True) := by
  have exponent : i = 3 ∨ i = 4 := by rcases pair with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp
  have select : RelCT isa (fun s t => CrtPowerSelection g bs1 child slot j s ∧
      CrtPowerSelection g bs2 child slot j t ∧ s.sp = t.sp) (selectChild slot) (fun _ _ => True) :=
    (crt_selectChild_ct slot).mono
      (fun _ _ h => ⟨h.1.selected.2.ptr.trans h.2.1.selected.2.ptr.symm, h.2.2⟩) (fun _ _ _ => trivial)
  intro s t tr1 tr2 u v h e1 e2
  have kind := h.1.kind
  exact crt_seq_ct select (fun s h => crt_selectPower_input s h i exponent)
    (fun s h => crt_selectPower_input s h i exponent)
    ((relCT_keep_sp ((crt_narrowPower_ct (kernel := kernel)) kind j i pair) (fun _ _ h => h.2.2)).seq crt_selectMain_ct)
    s t tr1 tr2 u v h e1 e2

end VG.Proof.Bignum.Arm
