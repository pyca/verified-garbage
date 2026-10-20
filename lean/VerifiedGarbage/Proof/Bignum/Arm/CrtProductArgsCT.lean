module
public import VerifiedGarbage.Proof.Bignum.Arm.CrtProductState
public import VerifiedGarbage.Proof.Framework.RelCT

import VerifiedGarbage.Proof.Bignum.Arm.CrtProductControl
import VerifiedGarbage.Proof.Bignum.Arm.CrtHeaderCopiesCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtCopyHeaderPointer
import VerifiedGarbage.Proof.Bignum.Arm.CrtCopyChildPointer
import VerifiedGarbage.Proof.Bignum.Arm.StageCT

/-! # Factor-product setup hides both factors while exposing only public buffer geometry -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt

theorem crt_productArgs_ct {base : BitVec 32} {size o a b cp cq w : Nat} {coefficient : Bool} (fit : 236 ≤ size) :
    RelCT isa (fun s t => CrtProductInput base size o a b cp cq w s coefficient ∧ CrtProductInput base size o a b cp cq w t coefficient)
      (productArgs coefficient) (fun _ _ => True) := by
  let P := fun s => CrtProductInput base size o a b cp cq w s coefficient
  have first : RelCT isa (fun s t => P s ∧ P t) (.block (copyChildPointer 224 128 (productOperandSlot coefficient))) (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    exact crt_copyChildPointer_ct (base := base) (child := base + BitVec.ofNat 32 cp)
      (size := size) (src := 224) (dst := 128) (by omega) (by decide) s t tr1 tr2 u v
      ⟨⟨h.1.workspace, h.1.ptr, h.1.pLink⟩, ⟨h.2.workspace, h.2.ptr, h.2.pLink⟩⟩ e1 e2
  have firstWP (s : State) (h : P s) : WP isa (.block (copyChildPointer 224 128 (productOperandSlot coefficient))) s P := by
    have before := h.pBeforeOut
    have outFit := h.outFits
    refine WP.mono (crt_copyChildPointer_ok s h.workspace (by omega) (by omega) (by decide) (by decide)
      (by cases coefficient <;> decide) (by omega) h.ptr h.pLink h.pArray) ?_
    rintro t ⟨mem, rest⟩
    exact h.after_control (by decide) (by decide) mem rest
  have second : RelCT isa (fun s t => P s ∧ P t) (.block (copyChildPointer 228 132)) (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    exact crt_copyChildPointer_ct (base := base) (child := base + BitVec.ofNat 32 cq)
      (size := size) (src := 228) (dst := 132) (by omega) (by decide) s t tr1 tr2 u v
      ⟨⟨h.1.workspace, h.1.ptr, h.1.qLink⟩, ⟨h.2.workspace, h.2.ptr, h.2.qLink⟩⟩ e1 e2
  have secondWP (s : State) (h : P s) : WP isa (.block (copyChildPointer 228 132)) s P := by
    have before := h.qBeforeOut
    have outFit := h.outFits
    refine WP.mono (crt_copyChildPointer_ok s h.workspace (by omega) (by omega) (by decide) (by decide)
      (by decide) (by omega) h.ptr h.qLink h.qArray) ?_
    rintro t ⟨mem, rest⟩
    exact h.after_control (by decide) (by decide) mem rest
  have third := (crt_copyHeaderPointer_ct 232 136).mono (P' := fun s t => P s ∧ P t)
    (fun _ _ h => h.1.ptr.trans h.2.ptr.symm) (fun _ _ _ => trivial)
  have thirdWP (s : State) (h : P s) : WP isa (.block (copyHeaderPointer 232 136)) s P := by
    refine WP.mono (crt_copyHeaderPointer_ok s h.workspace (by omega) (by omega) (by decide) (by decide) h.ptr h.product) ?_
    rintro t ⟨mem, rest⟩
    exact h.after_control (by decide) (by decide) mem rest
  have last := crt_productCount_ct.mono (P' := fun s t => P s ∧ P t)
    (fun _ _ h => h.1.ptr.trans h.2.ptr.symm) (fun _ _ _ => trivial)
  exact (pair_posts first firstWP).seq ((pair_posts second secondWP).seq ((pair_posts third thirdWP).seq last))

end VG.Proof.Bignum.Arm
