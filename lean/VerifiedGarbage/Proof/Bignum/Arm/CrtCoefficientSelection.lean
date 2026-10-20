module
public import VerifiedGarbage.Impl.Bignum.Arm.CrtFn
public import VerifiedGarbage.Proof.Bignum.Arm.CrtCoefficient
public import VerifiedGarbage.Proof.Bignum.Arm.CrtPoweredState
public import VerifiedGarbage.Proof.Bignum.Arm.CrtStageCT

import VerifiedGarbage.Proof.Bignum.Arm.CrtImportQResidue
import VerifiedGarbage.Proof.Bignum.Arm.CrtSavedSources
import VerifiedGarbage.Proof.Bignum.Arm.CrtSelectWorkspace
import VerifiedGarbage.Proof.Bignum.Arm.CrtLayout

/-! # Preserve coefficient preconditions through workspace selection and residue import -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt

def CrtCoefficientSelection (g : CrtGeometry) (bs : Fin 7 → List Byte) (child : BitVec 32) (s : State) : Prop :=
  CrtSelected g bs child s ∧ ∃ M value,
    CrtPoweredState (crtP g.base g.words) (workspaceWords g.words) g.words M value s.mem ∧ M % 2 = 1 ∧ value < M

theorem crt_selectCoefficient_ready (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtCoefficientSelection g bs g.base s) :
    WP isa (selectChild 224) s (CrtCoefficientSelection g bs (crtP g.base g.words)) := by
  refine WP.mono (crt_selectLinked_ready s h.1.1 h.1.1.buffers.context.p h.1.1.p (by simp [crtRegions])
    (by have := h.1.1.buffers.context.size; omega : 224 + 4 ≤ 8 * workspaceWords g.words)
    (by decide) h.1.2.ptr h.1.1.main.p) ?_
  rintro t ⟨sharedT, readyT, frame, _⟩
  obtain ⟨M, value, powered, odd, bound⟩ := h.2
  exact ⟨⟨sharedT, readyT⟩, M, value,
    powered.congr (h.1.1.workspace_eq_after_base h.1.1.buffers.context.p (by simp [crtRegions]) frame), odd, bound⟩

theorem crt_importCoefficient_ready (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtCoefficientSelection g bs (crtP g.base g.words) s) :
    WP isa (.seq (.block CrtFn.qSource) (transferArray 1 6)) s
      (fun t => ∃ M, CrtCoefficientInput (crtP g.base g.words) g.qi (workspaceWords g.words) g.words g.pLength M (bs 6) t) := by
  obtain ⟨M, value, powered, odd, bound⟩ := h.2
  refine WP.mono (crt_importQResidue_ok s h.1.1 h.1.2 powered) ?_
  rintro t ⟨sharedT, readyT, poweredT, _, _, _⟩
  exact ⟨M, ⟨⟨poweredT.ready readyT, poweredT.modulus, odd, poweredT.r2, poweredT.one,
    by rw [poweredT.result]; exact bound⟩,
    sharedT.savedOperand 5 (by simp [crtRegions]), sharedT.buffers.pPositive,
    by have := sharedT.buffers.pShort; have := (crt_width_valid sharedT.buffers.lengthValid).2.2
       change _ ≤ 8 * Spec.Rsa.modulusWords g.length; omega⟩⟩

end VG.Proof.Bignum.Arm
