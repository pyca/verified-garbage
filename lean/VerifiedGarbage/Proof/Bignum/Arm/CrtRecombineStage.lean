module

public import VerifiedGarbage.Impl.Bignum.Arm.CrtFn
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Proof.Bignum.Arm.SanitizeModulusCT
public import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedState

import VerifiedGarbage.Proof.Bignum.Arm.CrtImportFinalResidue
import VerifiedGarbage.Proof.Bignum.Arm.CrtRecombineGeometry
import VerifiedGarbage.Proof.Bignum.Arm.CrtValidationPreserved
import VerifiedGarbage.Proof.Bignum.Arm.CrtProductValues
import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedWorkspace
import VerifiedGarbage.Proof.Bignum.Arm.CrtStorage
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Arm.CrtRecombineProduct
import VerifiedGarbage.Impl.Bignum.Arm.CrtRecombine
/-! # Reconstruct the integer result from the coefficient and q residue -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtRecombine.lean`, which only this module imported.
section

/-! # Exact wide CRT reconstruction, including all buffer initialization -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

theorem crt_recombine_ok (s : State) {base : BitVec 32} {size len w o a b cp cq d : Nat}
    (h : CrtRecombineInput base size len w o a b cp cq d s) :
    WP isa recombine s fun t =>
      val32 t.mem (State.addr base) o (4 * w + 2) =
        val32 s.mem (State.addr base) a (2 * w) * val32 s.mem (State.addr base) b (2 * w) +
        numAt s.mem (State.addr base) w 1 ∧
      Outs (State.addr base) [(128, 20), (o, 4 * (4 * w + 2)), (d, 4 * (4 * w + 2))] s.mem t.mem ∧
      Frame [⟨State.addr base, size⟩] s.mem t.mem ∧ t.gpr .r0 = base ∧ Rest roundClobbers s t := by
  rw [recombine, WP.seq_iff]
  refine WP.mono (crt_recombineProduct_ready s h) ?_
  rintro u ⟨ready, product, residue, outside, frame, rest⟩
  refine WP.mono (crt_finishRecombine_ok u ready) ?_
  rintro t ⟨value, outsideT, frameT, ptrT, restT⟩
  rw [product, residue] at value
  refine ⟨value, (outside.mono ?_).trans (outsideT.mono ?_), frame.trans frameT, ptrT, rest.trans restT⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl <;> simp
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl <;> simp

end VG.Proof.Bignum.Arm
end

end

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

theorem crt_recombineStage_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtShared g bs s) (ready : LayoutFrameReady g.base (workspaceWords g.words) g.words s) :
    WP isa (.seq (.seq (.block CrtFn.qSource) (transferArray 1 6)) recombine) s fun t =>
      CrtShared g bs t ∧ LayoutFrameReady g.base (workspaceWords g.words) g.words t ∧
      val32 t.mem (State.addr g.base) (productOffset g.words) (4 * g.words + 2) =
        numAt s.mem (State.addr (crtP g.base g.words)) g.words 5 *
        numAt s.mem (State.addr (crtQ g.base g.words)) g.words 0 +
        numAt s.mem (State.addr (crtQ g.base g.words)) g.words 6 ∧
      Frame [⟨State.addr g.base, g.size⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [WP.seq_iff]
  refine WP.mono (crt_importFinalResidue_ok s h ready) ?_
  rintro u ⟨sharedU, readyU, residue, frameU, restU⟩
  have pEq := h.workspace_eq_after h.buffers.context.p (by simp [crtRegions]) h.buffers.context.sepMP.symm (frameU.mono (by simp))
  have qEq := h.workspace_eq_after h.buffers.context.q (by simp [crtRegions]) h.buffers.context.sepMQ.symm (frameU.mono (by simp))
  refine WP.mono (crt_recombine_ok u (sharedU.recombine_input readyU)) ?_
  rintro t ⟨value, outside, frameT, ptr, restT⟩
  obtain ⟨pVal, qVal⟩ := sharedU.product_values true
  simp only [↓reduceIte] at pVal
  rw [pVal, qVal, pEq.number h.buffers.context.arraysFit (by decide : 5 < 8),
    qEq.number h.buffers.context.arraysFit (by decide : 0 < 8), residue] at value
  have writes : Outs (State.addr g.base) (crtValidationWrites g.words) u.mem t.mem := outside.mono (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [crtValidationWrites])
  have sharedT := sharedU.after_validation writes frameT restT
  have readyT : LayoutFrameReady g.base (workspaceWords g.words) g.words t :=
    ⟨⟨sharedT.buffers.context.main, sharedT.main.layout, sharedT.main.width, ptr⟩,
      by rw [restT.rd, restT.wr, restT.sp]; exact readyU.stackRead,
      by rw [restT.sp]; exact readyU.stackSep,
      saved_base_kept frameT (sharedU.stack.separate.sub_left (Region.sub_prefix (by decide))) readyU.saved restT.sp⟩
  have frameU' : Frame [⟨State.addr g.base, g.size⟩] s.mem u.mem := frameU.sub (by
    intro r hr; simp only [List.mem_singleton] at hr; subst r
    exact ⟨_, List.mem_singleton_self _, crt_region_sub_workspace h.buffers.workspace h.buffers.storageFits (by simp [crtRegions])⟩)
  exact ⟨sharedT, readyT, value, frameU'.trans frameT, restU.trans restT⟩

end VG.Proof.Bignum.Arm
