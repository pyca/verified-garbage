module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtCoefficientSelection
import VerifiedGarbage.Proof.Bignum.Arm.CrtCoefficientCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtImportResidueCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtSelectStageCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtWorkspaceCallCT
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.Arm.SquareRedCT

/-! # The coefficient phase hides both residues, p and qInv -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt
open VG.Spec.Rsa.Mont (arrAt)

theorem crt_coefficientStage_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} :
    RelCT isa (fun s t => CrtCoefficientSelection g bs1 g.base s ∧
      CrtCoefficientSelection g bs2 g.base t ∧ s.sp = t.sp) CrtFn.coefficientPhase (fun _ _ => True) := by
  have select : RelCT isa (fun s t => CrtCoefficientSelection g bs1 g.base s ∧
      CrtCoefficientSelection g bs2 g.base t ∧ s.sp = t.sp) (selectChild 224) (fun _ _ => True) :=
    (crt_select_stage_ct 224).mono (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ _ => trivial)
  have transfer : RelCT isa (fun s t => CrtCoefficientSelection g bs1 (crtP g.base g.words) s ∧
      CrtCoefficientSelection g bs2 (crtP g.base g.words) t ∧ s.sp = t.sp)
      (.seq (.block CrtFn.qSource) (transferArray 1 6)) (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    exact crt_importResidue_ct h.1.1.1.buffers.context.sepPQ.symm s t tr1 tr2 u v ⟨h.1.1, h.2.1.1, h.2.2⟩ e1 e2
  let Input := fun (bs : Fin 7 → List Byte) (s : State) =>
    ∃ M, CrtCoefficientInput (crtP g.base g.words) g.qi (workspaceWords g.words) g.words g.pLength M (bs 6) s
  have coeff : RelCT isa (fun s t => Input bs1 s ∧ Input bs2 t ∧ s.sp = t.sp) coefficient (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    obtain ⟨⟨M1, h1⟩, ⟨M2, h2⟩, sp⟩ := h
    have fit : arrAt g.words 3 + 32 ≤ 8 * workspaceWords g.words := by
      have width := h1.difference.ready.width ▸ h1.difference.ready.layout.2.2.1
      have end3 := Nat.le_trans (array_end_le (w := g.words) (by decide : 3 < 8)) width
      have wpos := h1.difference.ready.width ▸ h1.difference.ready.layout.1
      omega
    exact crt_coefficient_ct fit s t tr1 tr2 u v ⟨h1, h2, sp⟩ e1 e2
  have tail := crt_seq_ct transfer (fun s h => crt_importCoefficient_ready s h)
    (fun s h => crt_importCoefficient_ready s h)
    ((relCT_keep_sp coeff (fun _ _ h => h.2.2)).seq crt_selectMain_ct)
  exact crt_seq_ct select (fun s h => crt_selectCoefficient_ready s h)
    (fun s h => crt_selectCoefficient_ready s h) tail.assoc

end VG.Proof.Bignum.Arm
