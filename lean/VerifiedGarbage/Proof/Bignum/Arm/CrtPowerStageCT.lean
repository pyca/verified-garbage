module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtPowerSelection
public import VerifiedGarbage.Proof.Bignum.Arm.CrtPrimePowerCT
public import VerifiedGarbage.Proof.Bignum.Arm.CrtWorkspaceCallCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # A selected factor power hides factor, exponent, input, and acceptance -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt
open VG.Spec.Rsa.Mont (arrAt)

theorem crt_powerStage_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} {child : BitVec 32} {slot : Nat}
    (count : 128 * g.words < 2 ^ 32) (i : Fin 6) (exponent : i = 3 ∨ i = 4) :
    RelCT isa (fun s t => CrtPowerSelection g bs1 child slot s ∧ CrtPowerSelection g bs2 child slot t ∧ s.sp = t.sp)
      (CrtFn.power slot (56 + 8 * i.val)) (fun _ _ => True) := by
  have select : RelCT isa (fun s t => CrtPowerSelection g bs1 child slot s ∧ CrtPowerSelection g bs2 child slot t ∧ s.sp = t.sp)
      (selectChild slot) (fun _ _ => True) :=
    (crt_selectChild_ct slot).mono
      (fun _ _ h => ⟨h.1.selected.2.ptr.trans h.2.1.selected.2.ptr.symm, h.2.2⟩) (fun _ _ _ => trivial)
  let Input := fun (bs : Fin 7 → List Byte) => CrtPrimePowerInput child g.input (g.source i.succ)
    (workspaceWords g.words) g.words g.length (g.sourceLength i.succ) (56 + 8 * i.val) (bs 1) (bs i.succ)
  have power : RelCT isa (fun s t => Input bs1 s ∧ Input bs2 t ∧ s.sp = t.sp)
      (primePower (56 + 8 * i.val)) (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    have width := h.1.accepted.width ▸ h.1.accepted.layout.2.2.1
    have fit : arrAt g.words 3 + 32 ≤ 8 * workspaceWords g.words := by
      have end3 := Nat.le_trans (array_end_le (w := g.words) (by decide : 3 < 8)) width
      have wpos := h.1.accepted.width ▸ h.1.accepted.layout.1
      omega
    exact crt_primePower_ct count fit
      (by rw [h.1.sources.exponent.length]; exact h.1.sources.exponentPositive)
      (h.1.sources.exponent.length.trans h.2.1.sources.exponent.length.symm)
      s t tr1 tr2 u v h e1 e2
  exact crt_seq_ct select (fun s h => crt_selectPower_input s h i exponent)
    (fun s h => crt_selectPower_input s h i exponent)
    ((relCT_keep_sp power (fun _ _ h => h.2.2)).seq crt_selectMain_ct)

end VG.Proof.Bignum.Arm
