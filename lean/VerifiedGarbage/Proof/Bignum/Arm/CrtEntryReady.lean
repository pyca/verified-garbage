module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtInput
public import VerifiedGarbage.Proof.Bignum.Arm.PcPush
public import VerifiedGarbage.Proof.Bignum.Arm.WindowKernel
public import VerifiedGarbage.Impl.Bignum.Arm.CrtFn
public import VerifiedGarbage.Proof.Bignum.Arm.CrtBodyInput
public import VerifiedGarbage.Proof.Bignum.Arm.CrtStorage
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Proof.Framework.RelCT

import VerifiedGarbage.Proof.Bignum.Arm.PublicPush
import VerifiedGarbage.Proof.Bignum.Arm.PcEntryMemory
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.Arm.CrtCheckedState
import Mathlib.Data.Int.ModEq
import VerifiedGarbage.Proof.Bignum.Arm.CrtPrepareState
import VerifiedGarbage.Proof.Bignum.Arm.CrtBegin
import VerifiedGarbage.Proof.Bignum.Arm.CrtStageCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtAcceptInput
import VerifiedGarbage.Proof.Bignum.Arm.CrtLoadPBody
import VerifiedGarbage.Proof.Bignum.Arm.CrtSavedSources
import VerifiedGarbage.Proof.Bignum.Arm.CrtLayout
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.Arm.SavedOperandLayoutCT
import VerifiedGarbage.Proof.Bignum.Arm.InputCompareLayoutCT
import VerifiedGarbage.Proof.Bignum.Arm.SaveAcceptanceCT
import VerifiedGarbage.Proof.Bignum.Arm.SavedOperandLayout
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.MergeAcceptanceCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtSelectStageCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtWorkspaceCallCT
import VerifiedGarbage.Impl.Bignum.Arm.CrtCheckProduct
import VerifiedGarbage.Proof.Bignum.Arm.CrtCheckProductState
import VerifiedGarbage.Proof.Bignum.Arm.CrtPadModulusCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtCompareProductCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtValidateProduct
import VerifiedGarbage.Proof.Bignum.Arm.CrtFactorProductCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtValidationGeometry
import VerifiedGarbage.Proof.Bignum.Arm.CrtLoadQStage
import VerifiedGarbage.Proof.Bignum.Arm.CrtLoadPStage
import VerifiedGarbage.Proof.Bignum.Arm.CrtAcceptStage
import VerifiedGarbage.Proof.Bignum.Arm.CrtCoefficientSelection
import VerifiedGarbage.Proof.Bignum.Arm.CrtFinishSelection
import VerifiedGarbage.Proof.Bignum.Arm.CrtResultBound
import VerifiedGarbage.Proof.Bignum.Arm.CrtBothPowers
import VerifiedGarbage.Proof.Bignum.Arm.CrtCoefficientStage
import VerifiedGarbage.Proof.Bignum.Arm.CrtAcceptedFactors
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Arm.CrtPowerSelection
import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowPowerCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtDifference
import VerifiedGarbage.Proof.Bignum.Arm.ReduceOperandCT
import VerifiedGarbage.Proof.Bignum.Arm.SubModArrayCT
import VerifiedGarbage.Proof.Bignum.Arm.ReduceOperand
import VerifiedGarbage.Impl.Bignum.Arm.CrtCoefficient
import VerifiedGarbage.Proof.Bignum.Arm.CrtInverseInput
import VerifiedGarbage.Proof.Bignum.Arm.SavedOperandCT
import VerifiedGarbage.Proof.Bignum.Arm.MontOpCT
import VerifiedGarbage.Proof.Bignum.Arm.SavedOperand
import VerifiedGarbage.Proof.Bignum.Arm.MontOp
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.CrtCoefficient
import VerifiedGarbage.Proof.Bignum.Arm.CrtImportResidueCT
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.Arm.SquareRedCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtFinishRecombine
import VerifiedGarbage.Proof.Bignum.Arm.CrtAddWideCT
import VerifiedGarbage.Impl.Bignum.Arm.CrtRecombine
import VerifiedGarbage.Proof.Bignum.Arm.CrtRecombineProduct
import VerifiedGarbage.Proof.Bignum.Arm.CrtRecombineGeometry
import VerifiedGarbage.Proof.Bignum.Arm.CrtImportFinalResidue
import VerifiedGarbage.Proof.Bignum.Arm.CrtOutputArgsCT
import VerifiedGarbage.Proof.Bignum.Arm.ExportBufferMaskedCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtPrepareCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtFailCT
import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheckCT
import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheck
import VerifiedGarbage.Proof.Bignum.Arm.CrtFinishStage
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Bignum.Arm.CrtCallStack
import VerifiedGarbage.Proof.Bignum.Arm.CrtFail
import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
/-! # Establish the private RSA body and saved-register invariants from native arguments -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtValidInput.lean`, which only this module imported.
section

/-! # Inputs to the private RSA path after checking the public modulus -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont

structure CrtValidInput (g : CrtGeometry) (bs : Fin 7 → List Byte) (s : State) : Prop where
  buffers : CrtBuffers g bs s
  stack : CrtCallStack g s
  ptr : s.gpr .r0 = g.base
  count : s.gpr .r6 = BitVec.ofNat 32 g.length
  saved : s.mem.readW (State.addr s.sp) 32 = g.base
  modulusPtr : s.mem.readW (off (State.addr s.sp) 8) 32 = g.modulus
  valid : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (bs 0)) g.length = true

theorem CrtValidInput.prepare_input {s : State} {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtValidInput g bs s) : CrtPrepareInput g.base g.modulus g.size g.words g.length (bs 0) s := by
  have mainSub : (⟨State.addr g.base, 8 * workspaceWords g.words⟩ : Region).Sub ⟨State.addr g.base, g.size⟩ :=
    crt_region_sub_workspace h.buffers.workspace h.buffers.storageFits (by simp [crtRegions])
  have source : SavedOperand g.base g.modulus (workspaceWords g.words) g.length 8 12 (bs 0) s :=
    ⟨h.stack.nowrap, ⟨h.stack.read (by decide), h.stack.read (by decide)⟩, h.stack.separate.sub_right mainSub, by decide, by decide,
      h.modulusPtr, h.stack.count, h.buffers.source 0, (h.buffers.sourceSeparate 0).sub_right mainSub⟩
  exact ⟨h.buffers.workspace, h.buffers.context, h.buffers.storageFits, source, h.stack.separate, h.buffers.sourceSeparate 0,
    by simpa only [off, BitVec.add_zero] using h.stack.read (d := 0) (by decide),
    h.stack.write (by decide), h.saved, h.ptr, h.count, h.buffers.lengthValid, rfl⟩

theorem crt_begin_selected (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtValidInput g bs s) : WP isa CrtFn.prepare s (CrtSelected g bs g.base) :=
  (crt_begin_ok s h.buffers h.stack h.ptr h.count h.saved h.modulusPtr h.valid).mono (fun _ j => ⟨j.1, j.2.1⟩)

theorem crt_validate_checked (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtSelected g bs g.base s) : WP isa CrtFn.validate s (CrtCheckedState g bs) :=
  (crt_validateStage_ok s h.1 h.2).mono (fun _ j => ⟨⟨j.1, j.2.1⟩, j.2.2.1, j.2.2.2.1, j.2.2.2.2.1⟩)

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtValidationInputs.lean`, which only this module imported.
section

/-! # Recover validation inputs from the selected workspace -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt

theorem CrtSelected.accept_input {s : State} {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtSelected g bs g.base s) : CrtAcceptInput g.base g.input (workspaceWords g.words) g.words g.length (bs 1) s := by
  have mainSub := crt_region_sub_workspace h.1.buffers.workspace h.1.buffers.storageFits
    (r := ⟨State.addr g.base, 8 * workspaceWords g.words⟩) (by simp [crtRegions])
  exact ⟨h.2, h.1.main, h.1.inputSaved (by simp [crtRegions]),
    by have := h.1.buffers.lengthValid.1; omega, (crt_width_valid h.1.buffers.lengthValid).2.2,
    by have := h.1.stack.nowrap; omega, h.1.stack.write (by decide),
    (h.1.stack.separate.symm.sub_right (Offset.sub_base _ (by decide))).sub_left mainSub⟩

theorem CrtSelected.loadP_input {s : State} {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtSelected g bs (crtP g.base g.words) s) :
    CrtLoadPInput (crtP g.base g.words) g.p g.qi (workspaceWords g.words) g.words g.pLength (bs 2) (bs 6) s :=
  ⟨h.2, h.1.savedOperand 1 (by simp [crtRegions]), h.1.savedOperand 5 (by simp [crtRegions]),
    h.1.buffers.pPositive,
    by have := h.1.buffers.pShort; have := (crt_width_valid h.1.buffers.lengthValid).2.2
       change _ ≤ 8 * Spec.Rsa.modulusWords g.length; omega,
    h.1.stack.write (by decide)⟩

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtAcceptInputCT.lean`, which only this module imported.
section

/-! # The CRT ciphertext range check and saved acceptance remain secret -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem crt_acceptInput_ct {base src : BitVec 32} {len w k : Nat} {bs1 bs2 : List Byte} :
    RelCT isa (fun s t => CrtAcceptInput base src len w k bs1 s ∧
      CrtAcceptInput base src len w k bs2 t ∧ s.sp = t.sp) CrtFn.acceptInput (fun _ _ => True) := by
  let P := fun s t => CrtAcceptInput base src len w k bs1 s ∧
    CrtAcceptInput base src len w k bs2 t ∧ s.sp = t.sp
  have load : RelCT isa P (savedOperand 1 56 12) (fun _ _ => True) :=
    (savedOperandLayout_ct (by decide : 1 < 8)).mono
      (fun _ _ h => ⟨⟨h.1.ready, h.1.source⟩, ⟨h.2.1.ready, h.2.1.source⟩, h.2.2⟩) (fun _ _ _ => trivial)
  have wp (s : State) {bs : List Byte} (h : CrtAcceptInput base src len w k bs s) :
      WP isa (savedOperand 1 56 12) s (LayoutFrameReady base len w) :=
    WP.mono (savedOperandLayout_ok s h.ready h.source (by decide : 1 < 8) h.positive h.fits) (fun _ j => j.1)
  have first := (relCT_keep_sp load (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨wp s h.1, wp t h.2.1⟩)
  have compare : RelCT isa (fun s t => s.sp = t.sp ∧ LayoutFrameReady base len w s ∧ LayoutFrameReady base len w t)
      inputCompare (fun _ _ => True) :=
    inputCompareLayout_ct.mono (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ _ => trivial)
  exact first.seq ((relCT_keep_sp compare (fun _ _ h => h.1)).seq saveAcceptance_ct)

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtLoadPBodyCT.lean`, which only this module imported.
section

/-! # Secret CRT factor and coefficient loading is constant-time -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem crt_loadPBody_ct {base pp qp : BitVec 32} {len w k : Nat} {pb1 qb1 pb2 qb2 : List Byte} :
    RelCT isa (fun s t => CrtLoadPInput base pp qp len w k pb1 qb1 s ∧
      CrtLoadPInput base pp qp len w k pb2 qb2 t ∧ s.sp = t.sp) CrtFn.loadPBody (fun _ _ => True) := by
  let P := fun s t => CrtLoadPInput base pp qp len w k pb1 qb1 s ∧
    CrtLoadPInput base pp qp len w k pb2 qb2 t ∧ s.sp = t.sp
  let Q := fun (bs : List Byte) (s : State) => LayoutFrameReady base len w s ∧
    SavedOperand base qp len k 96 100 bs s ∧ 0 < k ∧ k ≤ 8 * w
  have firstCT : RelCT isa P (savedOperand 0 64 68) (fun _ _ => True) :=
    (savedOperandLayout_ct (by decide : 0 < 8)).mono
      (fun _ _ h => ⟨⟨h.1.ready, h.1.prime⟩, ⟨h.2.1.ready, h.2.1.prime⟩, h.2.2⟩) (fun _ _ _ => trivial)
  have firstWP (s : State) {pb qb : List Byte} (h : CrtLoadPInput base pp qp len w k pb qb s) :
      WP isa (savedOperand 0 64 68) s (Q qb) := by
    refine WP.mono (savedOperandLayout_ok s h.ready h.prime (by decide : 0 < 8) h.positive h.fits) ?_
    rintro t ⟨ready, _, _, frame, rest⟩
    exact ⟨ready, h.inverse.after_workspace frame rest, h.positive, h.fits⟩
  have first := (relCT_keep_sp firstCT (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨firstWP s h.1, firstWP t h.2.1⟩)
  have secondCT : RelCT isa (fun s t => s.sp = t.sp ∧ Q qb1 s ∧ Q qb2 t)
      (savedOperand 1 96 100) (fun _ _ => True) :=
    (savedOperandLayout_ct (by decide : 1 < 8)).mono
      (fun _ _ h => ⟨⟨h.2.1.1, h.2.1.2.1⟩, ⟨h.2.2.1, h.2.2.2.1⟩, h.1⟩) (fun _ _ _ => trivial)
  have secondWP (s : State) {qb : List Byte} (h : Q qb s) :
      WP isa (savedOperand 1 96 100) s (LayoutFrameReady base len w) :=
    WP.mono (savedOperandLayout_ok s h.1 h.2.1 (by decide : 1 < 8) h.2.2.1 h.2.2.2) (fun _ j => j.1)
  have second := (relCT_keep_sp secondCT (fun _ _ h => h.1)).wp
    (fun s t h => ⟨secondWP s h.2.1, secondWP t h.2.2⟩)
  have compare : RelCT isa (fun s t => s.sp = t.sp ∧ LayoutFrameReady base len w s ∧ LayoutFrameReady base len w t)
      inputCompare (fun _ _ => True) :=
    inputCompareLayout_ct.mono (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ _ => trivial)
  exact first.seq (second.seq ((relCT_keep_sp compare (fun _ _ h => h.1)).seq mergeAcceptance_ct))

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtValidationStagesCT.lean`, which only this module imported.
section

/-! # The private RSA validation stages hide all key and ciphertext bytes -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt

theorem crt_acceptStage_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} :
    RelCT isa (fun s t => CrtSelected g bs1 g.base s ∧ CrtSelected g bs2 g.base t ∧ s.sp = t.sp)
      CrtFn.acceptInput (fun _ _ => True) :=
  crt_acceptInput_ct.mono (fun _ _ h => ⟨h.1.accept_input, h.2.1.accept_input, h.2.2⟩) (fun _ _ _ => trivial)

theorem crt_loadPStage_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} :
    RelCT isa (fun s t => CrtSelected g bs1 g.base s ∧ CrtSelected g bs2 g.base t ∧ s.sp = t.sp)
      CrtFn.loadP (fun _ _ => True) := by
  have body : RelCT isa (fun s t => CrtSelected g bs1 (crtP g.base g.words) s ∧
      CrtSelected g bs2 (crtP g.base g.words) t ∧ s.sp = t.sp) CrtFn.loadPBody (fun _ _ => True) :=
    crt_loadPBody_ct.mono (fun _ _ h => ⟨h.1.loadP_input, h.2.1.loadP_input, h.2.2⟩) (fun _ _ _ => trivial)
  exact crt_seq_ct (crt_select_stage_ct 224) (fun s h => crt_selectP_stage s h) (fun s h => crt_selectP_stage s h)
    ((relCT_keep_sp body (fun _ _ h => h.2.2)).seq crt_selectMain_ct)

theorem crt_loadQStage_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} :
    RelCT isa (fun s t => CrtSelected g bs1 g.base s ∧ CrtSelected g bs2 g.base t ∧ s.sp = t.sp)
      CrtFn.loadQ (fun _ _ => True) := by
  have load : RelCT isa (fun s t => CrtSelected g bs1 (crtQ g.base g.words) s ∧
      CrtSelected g bs2 (crtQ g.base g.words) t ∧ s.sp = t.sp) (savedOperand 0 72 76) (fun _ _ => True) :=
    (savedOperandLayout_ct (by decide : 0 < 8)).mono
      (fun _ _ h => ⟨⟨h.1.2, h.1.1.savedOperand 2 (by simp [crtRegions])⟩,
        ⟨h.2.1.2, h.2.1.1.savedOperand 2 (by simp [crtRegions])⟩, h.2.2⟩) (fun _ _ _ => trivial)
  exact crt_seq_ct (crt_select_stage_ct 228) (fun s h => crt_selectQ_stage s h) (fun s h => crt_selectQ_stage s h)
    ((relCT_keep_sp load (fun _ _ h => h.2.2)).seq crt_selectMain_ct)

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtCheckProductCT.lean`, which only this module imported.
section

/-! # Combined modulus padding and product validation are constant-time -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt

theorem crt_checkProduct_ct {base : BitVec 32} {size len o a d w : Nat}
    (fit : 244 ≤ size) :
    RelCT isa (fun s t => CrtCheckProductInput base size len o a d w s ∧
      CrtCheckProductInput base size len o a d w t ∧ s.sp = t.sp) checkProduct (fun _ _ => True) := by
  let P := CrtCheckProductInput base size len o a d w
  have pad : RelCT isa (fun (s t : State) => P s ∧ P t ∧ s.sp = t.sp) padModulus (fun _ _ => True) :=
    (crt_padModulus_ct (base := base) (size := size) (len := len) (w := w) (d := d) fit).mono
      (fun _ _ h => ⟨h.1.padding, h.2.1.padding, h.2.2⟩) (fun _ _ _ => trivial)
  have ready := (relCT_keep_sp pad (fun _ _ h => h.2.2)).wp (fun s t h =>
    ⟨(crt_padComparison_ready s h.1).mono (fun _ j => j.1),
      (crt_padComparison_ready t h.2.1).mono (fun _ j => j.1)⟩)
  exact ready.seq (crt_compareProduct_ct.mono
    (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ _ => trivial))

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtValidateProductCT.lean`, which only this module imported.
section

/-! # Complete factor-product validation is constant-time -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt

theorem crt_validateProduct_ct {base : BitVec 32} {size len product cmp pad a b cp cq w : Nat}
    (fit : 244 ≤ size) :
    RelCT isa (fun s t => CrtValidateInput base size len product cmp pad a b cp cq w s ∧
      CrtValidateInput base size len product cmp pad a b cp cq w t ∧ s.sp = t.sp)
      validateProduct (fun _ _ => True) := by
  let P := CrtValidateInput base size len product cmp pad a b cp cq w
  have multiply : RelCT isa (fun (s t : State) => P s ∧ P t ∧ s.sp = t.sp)
      factorProduct (fun _ _ => True) :=
    (crt_factorProduct_ct (size := size) (by omega)).mono (fun _ _ h => ⟨h.1.multiplication, h.2.1.multiplication, h.2.2⟩)
      (fun _ _ _ => trivial)
  have ready := (relCT_keep_sp multiply (fun _ _ h => h.2.2)).wp (fun s t h =>
    ⟨(crt_validationProduct_ready s h.1).mono (fun _ j => j.1),
      (crt_validationProduct_ready t h.2.1).mono (fun _ j => j.1)⟩)
  exact ready.seq ((crt_checkProduct_ct fit).mono
    (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ _ => trivial))

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtValidateStageCT.lean`, which only this module imported.
section

/-! # The complete private key validation leaks no secret validation result -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt

theorem crt_productStage_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} :
    RelCT isa (fun s t => CrtSelected g bs1 g.base s ∧ CrtSelected g bs2 g.base t ∧ s.sp = t.sp)
      (.seq validateProduct (.block mergeAcceptance)) (fun _ _ => True) := by
  have product : RelCT isa (fun s t => CrtSelected g bs1 g.base s ∧ CrtSelected g bs2 g.base t ∧ s.sp = t.sp)
      validateProduct (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    have fit := (h.1.1.compare_input h.1.2).fit
    exact crt_validateProduct_ct fit s t tr1 tr2 u v
      ⟨h.1.1.validate_input h.1.2, h.2.1.1.validate_input h.2.1.2, h.2.2⟩ e1 e2
  exact (relCT_keep_sp product (fun _ _ h => h.2.2)).seq mergeAcceptance_ct

theorem crt_validateStage_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} :
    RelCT isa (fun s t => CrtSelected g bs1 g.base s ∧ CrtSelected g bs2 g.base t ∧ s.sp = t.sp)
      CrtFn.validate (fun _ _ => True) := by
  have acceptWP (s : State) {bs : Fin 7 → List Byte} (h : CrtSelected g bs g.base s) :
      WP isa CrtFn.acceptInput s (CrtSelected g bs g.base) :=
    (crt_acceptStage_ok s h.1 h.2).mono (fun _ j => ⟨j.1, j.2.1⟩)
  have pWP (s : State) {bs : Fin 7 → List Byte} (h : CrtSelected g bs g.base s) :
      WP isa CrtFn.loadP s (CrtSelected g bs g.base) :=
    (crt_loadPStage_ok s h.1 h.2).mono (fun _ j => ⟨j.1, j.2.1⟩)
  have qWP (s : State) {bs : Fin 7 → List Byte} (h : CrtSelected g bs g.base s) :
      WP isa CrtFn.loadQ s (CrtSelected g bs g.base) :=
    (crt_loadQStage_ok s h.1 h.2).mono (fun _ j => ⟨j.1, j.2.1⟩)
  exact crt_seq_ct crt_acceptStage_ct (fun s h => acceptWP s h) (fun s h => acceptWP s h)
    (crt_seq_ct crt_loadPStage_ct (fun s h => pWP s h) (fun s h => pWP s h)
      (crt_seq_ct crt_loadQStage_ct (fun s h => qWP s h) (fun s h => qWP s h) crt_productStage_ct))

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtComputeSelection.lean`, which only this module imported.
section

/-! # Retain safe private arithmetic and output bounds between the computation stages -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont

structure CrtPoweredPair (g : CrtGeometry) (bs : Fin 7 → List Byte) (s : State) : Prop where
  selected : CrtSelected g bs g.base s
  p : CrtPoweredState (crtP g.base g.words) (workspaceWords g.words) g.words (crtFactor bs 2)
    (Spec.Rsa.powMod (Spec.Rsa.os2ip (bs 1)) (Spec.Rsa.os2ip (bs 4)) (crtFactor bs 2)) s.mem
  q : CrtPoweredState (crtQ g.base g.words) (workspaceWords g.words) g.words (crtFactor bs 3)
    (Spec.Rsa.powMod (Spec.Rsa.os2ip (bs 1)) (Spec.Rsa.os2ip (bs 5)) (crtFactor bs 3)) s.mem
  flag : s.mem.readW (off (State.addr s.sp) 48) 32 = (if crtAccepted bs then 1 else 0)

theorem CrtPoweredPair.odd {s : State} {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtPoweredPair g bs s) : crtFactor bs 2 % 2 = 1 := by
  by_cases accepted : crtAccepted bs
  · simpa only [crtFactor, ite_eq_left accepted] using (h.selected.1.accepted_factors accepted).1.2
  · simp [crtFactor, accepted]

theorem CrtPoweredPair.bound {s : State} {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtPoweredPair g bs s) :
    Spec.Rsa.powMod (Spec.Rsa.os2ip (bs 1)) (Spec.Rsa.os2ip (bs 4)) (crtFactor bs 2) < crtFactor bs 2 := by
  rw [powMod_eq]; exact Nat.mod_lt _ (by have := h.p.positive; omega)

theorem CrtPoweredPair.coefficientSelection {s : State} {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtPoweredPair g bs s) : CrtCoefficientSelection g bs g.base s :=
  ⟨h.selected, _, _, h.p, h.odd, h.bound⟩

theorem crt_bothPowers_ready (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtCheckedState g bs s) (kernel : WindowKernel := baselineWindowKernel) :
    WP isa (.seq ((CrtFn.powerWith kernel.code) 224 64 80) ((CrtFn.powerWith kernel.code) 228 72 88)) s (CrtPoweredPair g bs) :=
  ((crt_bothPowers_ok (kernel := kernel)) s h.selected.1 h.selected.2 h.p h.q h.flag).mono
    (fun _ j => ⟨⟨j.1, j.2.1⟩, j.2.2.1, j.2.2.2.1, j.2.2.2.2.1⟩)

theorem crt_coefficientFinish_ready (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtPoweredPair g bs s) : WP isa CrtFn.coefficientPhase s (CrtFinishSelection g bs) := by
  refine WP.mono (crt_coefficientStage_ok s h.selected.1 h.selected.2 h.p h.q h.odd h.bound) ?_
  rintro t ⟨sharedT, readyT, _, coefficient, qT, flagT, _, _⟩
  refine ⟨⟨sharedT, readyT⟩, decide (crtAccepted bs), ?_, ?_⟩
  · rw [flagT, h.flag]
    by_cases ac : crtAccepted bs <;> simp [ac]
  · intro accepted
    have ac : crtAccepted bs := of_decide_eq_true accepted
    have reconstruction : crtReconstruction g t.mem = crtPrivateValue bs := by
      unfold crtReconstruction
      rw [coefficient, qT.modulus, qT.result]
      simp only [crtFactor, ite_eq_left ac, powMod_eq, crtPrivateValue, crtResult]
      rw [Nat.mul_comm]
      exact Nat.add_comm _ _
    rw [reconstruction]
    exact h.selected.1.result_fits ac

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtPowerStageCT.lean`, which only this module imported.
section

/-! # A selected factor power hides factor, exponent, input, and acceptance -/

section

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
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtBothPowersCT.lean`, which only this module imported.
section

/-! # Both private powers have identical traces for independent secret keys -/

section

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
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtDifferenceCT.lean`, which only this module imported.
section

/-! # CRT residue subtraction hides both residues and the secret factor -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt
open VG.Spec.Rsa.Mont (arrAt Operand)

theorem crt_difference_ct {base : BitVec 32} {len w M1 M2 : Nat} (fit : arrAt w 3 + 32 ≤ 8 * len) :
    RelCT isa (fun s t => CrtDifferenceInput base len w M1 s ∧ CrtDifferenceInput base len w M2 t ∧ s.sp = t.sp)
      difference (fun _ _ => True) := by
  let P := fun (s t : State) => CrtDifferenceInput base len w M1 s ∧ CrtDifferenceInput base len w M2 t ∧ s.sp = t.sp
  have op1 : Operand 1 := by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]
  have input (s : State) {M : Nat} (h : CrtDifferenceInput base len w M s) : ReduceOperandReady base len w s := by
    have positive : 0 < M := by have := h.ready.modulus; rw [h.modulus] at this; omega
    exact ⟨h.ready, by rw [h.r2, h.modulus]; exact Nat.mod_lt _ positive,
      by rw [h.one]; exact h.ready.modulus⟩
  have reduce : RelCT isa P (reduceOperand 1) (fun _ _ => True) :=
    (reduceOperand_ct op1 (by decide) (by decide) fit).mono
      (fun s t h => ⟨input s h.1, input t h.2.1, h.2.2⟩) (fun _ _ _ => trivial)
  have wp (s : State) {M : Nat} (h : CrtDifferenceInput base len w M s) :
      WP isa (reduceOperand 1) s (ArithmeticReady base len w) :=
    (reduceOperand_ok s h.ready op1 (by decide) (by decide) h.modulus h.odd h.r2 h.one).mono (fun _ j => j.1)
  have reduced := (relCT_keep_sp reduce (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨wp s h.1, wp t h.2.1⟩)
  have small : 128 ≤ 8 * len := by simp only [arrAt, Spec.Rsa.Mont.hdrBytes] at fit; omega
  exact reduced.seq ((subModArray_ct (o := 5) (a := 6) (b := 1)
    (by decide) (by decide) (by decide) (by decide) small).mono
    (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ _ => trivial))

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtTimesInverseCT.lean`, which only this module imported.
section

/-! # Loading and multiplying by qInv exposes no inverse or residue values -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt
open VG.Spec.Rsa.Mont (numAt arrAt Operand)

theorem crt_timesInverse_ct {base src : BitVec 32} {len w k M1 M2 : Nat} {bs1 bs2 : List Byte}
    (fit : arrAt w 3 + 32 ≤ 8 * len) :
    RelCT isa (fun s t => CrtInverseInput base src len w k M1 bs1 s ∧
      CrtInverseInput base src len w k M2 bs2 t ∧ s.sp = t.sp) timesInverse (fun _ _ => True) := by
  let P := fun (s t : State) => CrtInverseInput base src len w k M1 bs1 s ∧
    CrtInverseInput base src len w k M2 bs2 t ∧ s.sp = t.sp
  let Q := fun (b : Nat) (s : State) => ArithmeticReady base len w s ∧
    numAt s.mem (State.addr base) w b < numAt s.mem (State.addr base) w 0
  have op (q : Nat) (hq : q = 0 ∨ q = 1 ∨ q = 4 ∨ q = 5) : Operand q := by
    rcases hq with rfl | rfl | rfl | rfl <;> simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]
  have load : RelCT isa P (savedOperand 1 96 100) (fun _ _ => True) :=
    (savedOperand_ct (base := base) (src := src) (len := len) (w := w) (k := k)
      (ps := 96) (cs := 100) (bs1 := bs1) (bs2 := bs2) (by decide : 1 < 8)).mono
      (fun _ _ h => ⟨⟨h.1.ready, h.1.source⟩, ⟨h.2.1.ready, h.2.1.source⟩, h.2.2⟩) (fun _ _ _ => trivial)
  have loadWP (s : State) {M : Nat} {bs : List Byte} (h : CrtInverseInput base src len w k M bs s) :
      WP isa (savedOperand 1 96 100) s (Q 4) := by
    have fits : arrAt w 8 ≤ 8 * len := h.ready.width ▸ h.ready.layout.2.2.1
    have positive : 0 < M := by have := h.ready.modulus; rw [h.modulus] at this; omega
    refine WP.mono (savedOperand_ok s h.ready h.source (by decide : 1 < 8) (by decide) h.positive h.fits) ?_
    rintro t ⟨ready, _, keeps, _, _⟩
    have modulus := (keeps_array_num keeps fits (op 0 (by decide)) (by decide)).trans h.modulus
    have r2 := (keeps_array_num keeps fits (op 4 (by decide)) (by decide)).trans h.r2
    exact ⟨ready, by rw [modulus, r2]; exact Nat.mod_lt _ positive⟩
  have first := (relCT_keep_sp load (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨loadWP s h.1, loadWP t h.2.1⟩)
  have encode : RelCT isa (fun (s t : State) => s.sp = t.sp ∧ Q 4 s ∧ Q 4 t)
      (montOp 1 1 4) (fun _ _ => True) :=
    (montOp_ct (op 1 (by decide)) (op 1 (by decide)) (op 4 (by decide)) fit).mono
      (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ _ => trivial)
  have encodeWP (s : State) (h : Q 4 s) : WP isa (montOp 1 1 4) s (Q 1) := by
    refine WP.mono (montOp_ok s h.1 (op 1 (by decide)) (op 1 (by decide)) (op 4 (by decide)) (by decide) h.2) ?_
    rintro t ⟨ready, modulus, bound, _, _, _, _⟩
    exact ⟨ready, by rw [modulus]; exact bound⟩
  have second := (relCT_keep_sp encode (fun _ _ h => h.1)).wp
    (fun s t h => ⟨encodeWP s h.2.1, encodeWP t h.2.2⟩)
  exact first.seq (second.seq ((montOp_ct (op 5 (by decide)) (op 5 (by decide)) (op 1 (by decide)) fit).mono
    (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ _ => trivial)))

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtCoefficientCT.lean`, which only this module imported.
section

/-! # Complete CRT coefficient computation hides all private data -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt
open VG.Spec.Rsa.Mont (arrAt)

theorem crt_coefficient_ct {base src : BitVec 32} {len w k M1 M2 : Nat} {bs1 bs2 : List Byte}
    (fit : arrAt w 3 + 32 ≤ 8 * len) :
    RelCT isa (fun s t => CrtCoefficientInput base src len w k M1 bs1 s ∧
      CrtCoefficientInput base src len w k M2 bs2 t ∧ s.sp = t.sp) coefficient (fun _ _ => True) := by
  let P := fun (s t : State) => CrtCoefficientInput base src len w k M1 bs1 s ∧
    CrtCoefficientInput base src len w k M2 bs2 t ∧ s.sp = t.sp
  have diff : RelCT isa P difference (fun _ _ => True) :=
    (crt_difference_ct fit).mono (fun _ _ h => ⟨h.1.difference, h.2.1.difference, h.2.2⟩) (fun _ _ _ => trivial)
  have ready := (relCT_keep_sp diff (fun _ _ h => h.2.2)).wp (fun s t h =>
    ⟨(crt_coefficientDifference_ready s h.1).mono (fun _ j => j.1),
      (crt_coefficientDifference_ready t h.2.1).mono (fun _ j => j.1)⟩)
  exact ready.seq ((crt_timesInverse_ct fit).mono
    (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ _ => trivial))

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtCoefficientStageCT.lean`, which only this module imported.
section

/-! # The coefficient phase hides both residues, p and qInv -/

section

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
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtFinishRecombineCT.lean`, which only this module imported.
section

/-! # Final CRT reconstruction hides the product and residue -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt

theorem crt_finishRecombine_ct {base : BitVec 32} {size len w o d : Nat} (fit : 244 ≤ size) :
    RelCT isa (fun s t => CrtFinishInput base size len w o d s ∧
      CrtFinishInput base size len w o d t ∧ s.sp = t.sp) finishRecombine (fun _ _ => True) := by
  let P := CrtFinishInput base size len w o d
  have pad : RelCT isa (fun s t => P s ∧ P t ∧ s.sp = t.sp) (padModulus 1) (fun _ _ => True) :=
    (crt_padModulus_ct fit 1).mono (fun _ _ h => ⟨h.1.padding, h.2.1.padding, h.2.2⟩) (fun _ _ _ => trivial)
  have wp (s : State) (h : P s) : WP isa (padModulus 1) s (CrtAddWideInput base size o d w) :=
    WP.mono (crt_finishPad_ready s h) (fun _ j => j.1)
  have first := (relCT_keep_sp pad (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨wp s h.1, wp t h.2.1⟩)
  exact first.seq (crt_addWide_ct.mono (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ _ => trivial))

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtRecombineCT.lean`, which only this module imported.
section

/-! # Full CRT reconstruction conceals both factors and residues -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt

theorem crt_recombine_ct {base : BitVec 32} {size len w o a b cp cq d : Nat} (fit : 244 ≤ size) :
    RelCT isa (fun s t => CrtRecombineInput base size len w o a b cp cq d s ∧
      CrtRecombineInput base size len w o a b cp cq d t ∧ s.sp = t.sp) recombine (fun _ _ => True) := by
  let P := CrtRecombineInput base size len w o a b cp cq d
  have product : RelCT isa (fun s t => P s ∧ P t ∧ s.sp = t.sp) (factorProduct true) (fun _ _ => True) :=
    (crt_factorProduct_ct (by omega : 236 ≤ size)).mono
      (fun _ _ h => ⟨h.1.multiplication, h.2.1.multiplication, h.2.2⟩) (fun _ _ _ => trivial)
  have wp (s : State) (h : P s) : WP isa (factorProduct true) s (CrtFinishInput base size len w o d) :=
    WP.mono (crt_recombineProduct_ready s h) (fun _ j => j.1)
  have first := (relCT_keep_sp product (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨wp s h.1, wp t h.2.1⟩)
  exact first.seq ((crt_finishRecombine_ct fit).mono
    (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ _ => trivial))

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtRecombineStageCT.lean`, which only this module imported.
section

/-! # Reconstruct the wide CRT result without leaking its inputs -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt

theorem crt_recombineStage_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} :
    RelCT isa (fun s t => CrtSelected g bs1 g.base s ∧ CrtSelected g bs2 g.base t ∧ s.sp = t.sp)
      (.seq (.seq (.block CrtFn.qSource) (transferArray 1 6)) recombine) (fun _ _ => True) := by
  have transfer : RelCT isa (fun s t => CrtSelected g bs1 g.base s ∧ CrtSelected g bs2 g.base t ∧ s.sp = t.sp)
      (.seq (.block CrtFn.qSource) (transferArray 1 6)) (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    exact crt_importResidue_ct h.1.1.buffers.context.sepMQ.symm s t tr1 tr2 u v h e1 e2
  have wp (s : State) {bs : Fin 7 → List Byte} (h : CrtSelected g bs g.base s) :
      WP isa (.seq (.block CrtFn.qSource) (transferArray 1 6)) s (CrtSelected g bs g.base) :=
    (crt_importFinalResidue_ok s h.1 h.2).mono (fun _ j => ⟨j.1, j.2.1⟩)
  have recombination : RelCT isa (fun s t => CrtSelected g bs1 g.base s ∧ CrtSelected g bs2 g.base t ∧ s.sp = t.sp)
      recombine (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    exact crt_recombine_ct (h.1.1.compare_input h.1.2).fit s t tr1 tr2 u v
      ⟨h.1.1.recombine_input h.1.2, h.2.1.1.recombine_input h.2.1.2, h.2.2⟩ e1 e2
  exact crt_seq_ct transfer (fun s h => wp s h) (fun s h => wp s h) recombination

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtFinishStageCT.lean`, which only this module imported.
section

/-! # Reconstruction and masked output hide both the result and acceptance -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem crt_finishStage_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} :
    RelCT isa (fun s t => CrtFinishSelection g bs1 s ∧ CrtFinishSelection g bs2 t ∧ s.sp = t.sp)
      CrtFn.finish (fun _ _ => True) := by
  have reconstruct : RelCT isa (fun s t => CrtFinishSelection g bs1 s ∧ CrtFinishSelection g bs2 t ∧ s.sp = t.sp)
      (.seq (.seq (.block CrtFn.qSource) (transferArray 1 6)) VG.Impl.Bignum.Arm.Crt.recombine) (fun _ _ => True) :=
    crt_recombineStage_ct.mono (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ _ => trivial)
  have args : RelCT isa (fun s t => CrtExportSelection g bs1 s ∧ CrtExportSelection g bs2 t ∧ s.sp = t.sp)
      (.block CrtFn.outputArgs) (fun _ _ => True) :=
    crt_outputArgs_ct.mono (fun _ _ h => ⟨h.1.1.2.ptr.trans h.2.1.1.2.ptr.symm, h.2.2⟩) (fun _ _ _ => trivial)
  exact (crt_seq_ct reconstruct (fun s h => crt_recombineExport_ready s h)
    (fun s h => crt_recombineExport_ready s h)
    (crt_seq_ct args (fun s h => crt_exportArgs_ready s h) (fun s h => crt_exportArgs_ready s h) exportBufferMasked_ct)).assoc.assoc

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtComputeStageCT.lean`, which only this module imported.
section

/-! # The complete private computation has a secret-independent trace -/

section

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
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtValidCT.lean`, which only this module imported.
section

/-! # The full private RSA path reveals no key, ciphertext, or rejection bit -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem crt_valid_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} (kernel : WindowKernel := baselineWindowKernel) :
    RelCT isa (fun s t => CrtValidInput g bs1 s ∧ CrtValidInput g bs2 t ∧ s.sp = t.sp)
      (CrtFn.validWith kernel.code) (fun _ _ => True) := by
  have prepare : RelCT isa (fun s t => CrtValidInput g bs1 s ∧ CrtValidInput g bs2 t ∧ s.sp = t.sp)
      CrtFn.prepare (fun _ _ => True) :=
    crt_prepare_ct.mono (fun _ _ h => ⟨h.1.prepare_input, h.2.1.prepare_input, h.2.2⟩) (fun _ _ _ => trivial)
  exact crt_seq_ct prepare (fun s h => crt_begin_selected s h) (fun s h => crt_begin_selected s h)
    (crt_seq_ct crt_validateStage_ct (fun s h => crt_validate_checked s h) (fun s h => crt_validate_checked s h)
      (crt_computeStage_ct (kernel := kernel)))

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtBodyCT.lean`, which only this module imported.
section

/-! # The private RSA body's only branch depends on the public modulus -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

structure CrtModulusChecked (g : CrtGeometry) (bs : Fin 7 → List Byte) (s : State) : Prop where
  input : CrtBodyInput g bs s
  flag : s.z = Spec.Rsa.modulusValid (Spec.Rsa.os2ip (bs 0)) g.length

theorem crt_modulusCheck_ready (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtBodyInput g bs s) : WP isa (.block modulusCheck) s (CrtModulusChecked g bs) := by
  refine WP.mono (modulusCheck_ok s h.buffers.lengthValid.1 h.buffers.lengthValid.2
    (h.buffers.source 0).fits (h.buffers.source 0).read h.source h.count) ?_
  rintro t ⟨flag, mem, rest⟩
  have nb : Spec.Rsa.bytesAt s.mem (State.addr g.modulus) g.length = bs 0 := (h.buffers.source 0).bytes
  change t.z = Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr g.modulus) g.length)) g.length at flag
  rw [nb] at flag
  exact ⟨h.of_mem mem rest ((rest.gpr .r0 (by simp)).trans h.ptr)
    ((rest.gpr .r4 (by simp)).trans h.source) ((rest.gpr .r6 (by simp)).trans h.count), flag⟩

theorem crt_body_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} (modulus : bs1 0 = bs2 0) (kernel : WindowKernel := baselineWindowKernel) :
    RelCT isa (fun s t => CrtBodyInput g bs1 s ∧ CrtBodyInput g bs2 t ∧ s.sp = t.sp)
      (CrtFn.bodyWith kernel.code) (fun _ _ => True) := by
  have check : RelCT isa (fun s t => CrtBodyInput g bs1 s ∧ CrtBodyInput g bs2 t ∧ s.sp = t.sp)
      (.block modulusCheck) (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    exact ⟨modulusCheck_ct s t tr1 tr2 u v trivial trivial
      ⟨h.1.source.trans h.2.1.source.symm, h.1.count.trans h.2.1.count.symm⟩ e1 e2, trivial⟩
  have ready := (relCT_keep_sp check (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨crt_modulusCheck_ready s h.1, crt_modulusCheck_ready t h.2.1⟩)
  refine ready.seq (RelCT.ite ?_ ?_ ?_)
  · intro s t h
    change some s.z = some t.z
    rw [h.2.1.flag, h.2.2.flag, modulus]
  · apply (crt_valid_ct (kernel := kernel) (g := g) (bs1 := bs1) (bs2 := bs2)).mono ?_ (fun _ _ _ => trivial)
    intro s t h
    have flag : s.z = true := Option.some.inj h.2
    have good := h.1.2.1.flag.symm.trans flag
    have good2 : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (bs2 0)) g.length = true := by rw [← modulus]; exact good
    let a := h.1.2.1.input
    let b := h.1.2.2.input
    exact ⟨⟨a.buffers, a.stack, a.ptr, a.count, a.saved, a.modulusPtr, good⟩,
      ⟨b.buffers, b.stack, b.ptr, b.count, b.saved, b.modulusPtr, good2⟩, h.1.1⟩
  · exact crt_fail_ct.mono (fun _ _ h => ⟨h.1.2.1.input, h.1.2.2.input, h.1.1⟩) (fun _ _ _ => trivial)

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtComputeStage.lean`, which only this module imported.
section

/-! # Private RSA computation through exact masked output -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Spec.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

theorem crt_computeStage_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtShared g bs s) (ready : LayoutFrameReady g.base (workspaceWords g.words) g.words s)
    (p : numAt s.mem (State.addr (crtP g.base g.words)) g.words 0 = Spec.Rsa.os2ip (bs 2))
    (q : numAt s.mem (State.addr (crtQ g.base g.words)) g.words 0 = Spec.Rsa.os2ip (bs 3))
    (flag : s.mem.readW (off (State.addr s.sp) 48) 32 = (if crtAccepted bs then 1 else 0)) (kernel : WindowKernel := baselineWindowKernel) :
    WP isa (CrtFn.computeWith kernel.code) s fun t =>
      Spec.Rsa.bytesAt t.mem (State.addr g.output) g.length =
        (if crtAccepted bs then Spec.Rsa.i2osp (crtPrivateValue bs) g.length else List.replicate g.length 0) ∧
      t.gpr .r0 = (if crtAccepted bs then 1 else 0) ∧
      Frame (crtLiveMutable g s.sp ++ [⟨State.addr g.output, g.length⟩]) s.mem t.mem ∧ Rest roundClobbers s t := by
  unfold CrtFn.computeWith
  apply WP.assoc
  rw [WP.seq_iff]
  refine WP.mono ((crt_bothPowers_ok (kernel := kernel)) s h ready p q flag) ?_
  rintro u ⟨sharedU, readyU, poweredP, poweredQ, flagU, frameU, restU⟩
  have odd : crtFactor bs 2 % 2 = 1 := by
    by_cases accepted : crtAccepted bs
    · simpa only [crtFactor, ite_eq_left accepted] using (h.accepted_factors accepted).1.2
    · simp [crtFactor, accepted]
  have bound : Spec.Rsa.powMod (Spec.Rsa.os2ip (bs 1)) (Spec.Rsa.os2ip (bs 4)) (crtFactor bs 2) < crtFactor bs 2 := by
    rw [powMod_eq]; exact Nat.mod_lt _ (by have := poweredP.positive; omega)
  rw [WP.seq_iff]
  refine WP.mono (crt_coefficientStage_ok u sharedU readyU poweredP poweredQ odd bound) ?_
  rintro v ⟨sharedV, readyV, _, coefficient, qV, flagV, frameV, restV⟩
  have reconstruction (accepted : crtAccepted bs) : crtReconstruction g v.mem = crtPrivateValue bs := by
    unfold crtReconstruction
    rw [coefficient, qV.modulus, qV.result]
    simp only [crtFactor, ite_eq_left accepted, powMod_eq, crtPrivateValue, crtResult]
    rw [Nat.mul_comm]
    exact Nat.add_comm _ _
  have flagExport : v.mem.readW (off (State.addr v.sp) 48) 32 = BitVec.ofNat 32 (decide (crtAccepted bs)).toNat := by
    rw [flagV, flagU]
    by_cases accepted : crtAccepted bs <;> simp [accepted]
  refine WP.mono (crt_finishStage_ok v sharedV readyV flagExport (by
    intro accepted
    have ac : crtAccepted bs := of_decide_eq_true accepted
    rw [reconstruction ac]; exact h.result_fits ac)) ?_
  rintro t ⟨bytes, status, frameT, restT⟩
  have bytesT : Spec.Rsa.bytesAt t.mem (State.addr g.output) g.length =
      (if crtAccepted bs then Spec.Rsa.i2osp (crtPrivateValue bs) g.length else List.replicate g.length 0) := by
    by_cases ac : crtAccepted bs
    · simpa only [ac, decide_true, ↓reduceIte, reconstruction ac] using bytes
    · simpa only [ac, decide_false, Bool.false_eq_true, ↓reduceIte] using bytes
  have statusT : t.gpr .r0 = (if crtAccepted bs then 1 else 0) := by
    by_cases ac : crtAccepted bs <;> simpa [ac] using status
  rw [restU.sp] at frameV
  exact ⟨bytesT, statusT,
    ((frameU.trans frameV).mono (by intro r hr; exact List.mem_append_left _ hr)).trans (frameT.mono (by simp [crtLiveMutable])),
    restU.trans (restV.trans restT)⟩

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtComputeResult.lean`, which only this module imported.
section

/-! # The computed output satisfies the shared private-CRT result specification -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem crt_computed_written {s t : State} {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtShared g bs s)
    (bytes : Spec.Rsa.bytesAt t.mem (State.addr g.output) g.length =
      (if crtAccepted bs then Spec.Rsa.i2osp (crtPrivateValue bs) g.length else List.replicate g.length 0))
    (status : t.gpr .r0 = (if crtAccepted bs then 1 else 0)) :
    Spec.Rsa.written t.mem (State.addr g.output) g.length (t.gpr .r0)
      (Spec.Rsa.privateCrt (bs 0) (bs 1) (bs 2) (bs 3) (bs 4) (bs 5) (bs 6)) := by
  have nLength : (bs 0).length = g.length := (h.buffers.source 0).length
  have accepted : crtAccepted bs ↔ Spec.Rsa.os2ip (bs 1) < Spec.Rsa.os2ip (bs 0) ∧
      Spec.Rsa.os2ip (bs 2) * Spec.Rsa.os2ip (bs 3) = Spec.Rsa.os2ip (bs 0) ∧
      Spec.Rsa.os2ip (bs 6) < Spec.Rsa.os2ip (bs 2) := by
    simp only [crtAccepted, and_comm]
  simp only [Spec.Rsa.privateCrt, nLength, h.valid, ↓reduceIte, decryptCrt_eq, ← accepted]
  by_cases ac : crtAccepted bs
  · simp only [ac, ↓reduceIte, Option.map_some, Spec.Rsa.written, status, crtPrivateValue] at bytes ⊢
    exact ⟨trivial, bytes⟩
  · simp only [ac, ↓reduceIte, Option.map_none, Spec.Rsa.written, status] at bytes ⊢
    exact ⟨trivial, bytes⟩

theorem crt_validatedCompute_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtShared g bs s) (ready : LayoutFrameReady g.base (VG.Impl.Bignum.Arm.Crt.workspaceWords g.words) g.words s) (kernel : WindowKernel := baselineWindowKernel) :
    WP isa (.seq CrtFn.validate (CrtFn.computeWith kernel.code)) s fun t =>
      Spec.Rsa.written t.mem (State.addr g.output) g.length (t.gpr .r0)
        (Spec.Rsa.privateCrt (bs 0) (bs 1) (bs 2) (bs 3) (bs 4) (bs 5) (bs 6)) ∧
      Frame (crtLiveMutable g s.sp ++ [⟨State.addr g.output, g.length⟩]) s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [WP.seq_iff]
  refine WP.mono (crt_validateStage_ok s h ready) ?_
  rintro u ⟨sharedU, readyU, p, q, flag, frameU, restU⟩
  refine WP.mono ((crt_computeStage_ok (kernel := kernel)) u sharedU readyU p q flag) ?_
  rintro t ⟨bytes, status, frameT, restT⟩
  rw [restU.sp] at frameT
  exact ⟨crt_computed_written h bytes status,
    (frameU.mono (fun _ hr => List.mem_append_left _ hr)).trans frameT, restU.trans restT⟩

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtValid.lean`, which only this module imported.
section

/-! # The complete private RSA path for a valid public modulus -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem crt_valid_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (buffers : CrtBuffers g bs s) (stack : CrtCallStack g s)
    (ptr : s.gpr .r0 = g.base) (count : s.gpr .r6 = BitVec.ofNat 32 g.length)
    (saved : s.mem.readW (State.addr s.sp) 32 = g.base)
    (modulusPtr : s.mem.readW (off (State.addr s.sp) 8) 32 = g.modulus)
    (valid : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (bs 0)) g.length = true) (kernel : WindowKernel := baselineWindowKernel) :
    WP isa (CrtFn.validWith kernel.code) s fun t =>
      Spec.Rsa.written t.mem (State.addr g.output) g.length (t.gpr .r0)
        (Spec.Rsa.privateCrt (bs 0) (bs 1) (bs 2) (bs 3) (bs 4) (bs 5) (bs 6)) ∧
      Frame (crtMutable g s.sp ++ [⟨State.addr g.output, g.length⟩]) s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [CrtFn.validWith, WP.seq_iff]
  refine WP.mono (crt_begin_ok s buffers stack ptr count saved modulusPtr valid) ?_
  rintro u ⟨sharedU, readyU, frameU, restU⟩
  refine WP.mono ((crt_validatedCompute_ok (kernel := kernel)) u sharedU readyU) ?_
  rintro t ⟨written, frameT, restT⟩
  rw [restU.sp] at frameT
  refine ⟨written, (frameU.mono (fun _ hr => List.mem_append_left _ hr)).trans (frameT.mono ?_), restU.trans restT⟩
  intro r hr
  simp only [crtLiveMutable, crtMutable, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
  rcases hr with (rfl | rfl | rfl) | rfl <;> simp

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtBody.lean`, which only this module imported.
section

/-! # Complete private RSA body including public modulus rejection -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

theorem crt_body_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} (h : CrtBodyInput g bs s) (kernel : WindowKernel := baselineWindowKernel) :
    WP isa (CrtFn.bodyWith kernel.code) s fun t =>
      Spec.Rsa.written t.mem (State.addr g.output) g.length (t.gpr .r0)
        (Spec.Rsa.privateCrt (bs 0) (bs 1) (bs 2) (bs 3) (bs 4) (bs 5) (bs 6)) ∧
      Frame (crtMutable g s.sp ++ [⟨State.addr g.output, g.length⟩]) s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [CrtFn.bodyWith, WP.seq_iff]
  refine WP.mono (modulusCheck_ok s h.buffers.lengthValid.1 h.buffers.lengthValid.2
    (h.buffers.source 0).fits (h.buffers.source 0).read h.source h.count) ?_
  rintro u ⟨flag, mem, rest⟩
  have nb : Spec.Rsa.bytesAt s.mem (State.addr g.modulus) g.length = bs 0 := (h.buffers.source 0).bytes
  change u.z = Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr g.modulus) g.length)) g.length at flag
  rw [nb] at flag
  have hu := h.of_mem mem rest ((rest.gpr .r0 (by decide)).trans h.ptr)
    ((rest.gpr .r4 (by decide)).trans h.source) ((rest.gpr .r6 (by decide)).trans h.count)
  refine WP.ite (Spec.Rsa.modulusValid (Spec.Rsa.os2ip (bs 0)) g.length) (by change some u.z = _; rw [flag]) ?_ ?_
  · intro valid
    refine WP.mono ((crt_valid_ok (kernel := kernel)) u hu.buffers hu.stack hu.ptr hu.count hu.saved hu.modulusPtr valid) ?_
    rintro t ⟨written, frame, restT⟩
    rw [mem, rest.sp] at frame
    exact ⟨written, frame, (rest.mono (by decide)).trans restT⟩
  · intro invalid
    refine WP.mono (crt_fail_ok u hu) ?_
    rintro t ⟨status, bytes, frame, restT⟩
    have failed : Spec.Rsa.privateCrt (bs 0) (bs 1) (bs 2) (bs 3) (bs 4) (bs 5) (bs 6) = none := by
      have nLength : (bs 0).length = g.length := (h.buffers.source 0).length
      simp only [Spec.Rsa.privateCrt, nLength, invalid, Bool.false_eq_true, ite_false]
    rw [failed]
    rw [mem] at frame
    exact ⟨⟨status, bytes⟩, frame.mono (by simp), (rest.mono (by simp [roundClobbers])).trans restT⟩

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtBodyScope.lean`, which only this module imported.
section

/-! # Run the CRT proof using only the caller's original scratch permissions -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

structure CrtScopedInput (g : CrtGeometry) (bs : Fin 7 → List Byte) (s : State) : Prop where
  workspace : Workspace s g.base g.size
  body : CrtBodyInput g bs (crtExpanded s g.base g.words)

theorem crt_body_scoped_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} (h : CrtScopedInput g bs s) (kernel : WindowKernel := baselineWindowKernel) :
    WP isa (CrtFn.bodyWith kernel.code) s fun t =>
      Spec.Rsa.written t.mem (State.addr g.output) g.length (t.gpr .r0)
        (Spec.Rsa.privateCrt (bs 0) (bs 1) (bs 2) (bs 3) (bs 4) (bs 5) (bs 6)) ∧
      Frame (crtMutable g s.sp ++ [⟨State.addr g.output, g.length⟩]) s.mem t.mem ∧ Rest roundClobbers s t := by
  obtain ⟨tr, t, run, written, frame, rest⟩ := (crt_body_ok (kernel := kernel)) _ h.body
  obtain ⟨write, read⟩ := crt_expanded_covers h.workspace h.body.buffers.storageFits
  refine ⟨tr, t.withRegions s.rd s.wr, ?_, written, frame, ?_⟩
  · simpa only [crtExpanded, State.withRegions_withRegions, State.withRegions_self] using VG.Arm.Exec.widen run read write
  · exact ⟨rest.gpr, rfl, rfl, rest.sp⟩

theorem crt_body_scoped_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} (modulus : bs1 0 = bs2 0) (kernel : WindowKernel := baselineWindowKernel) :
    RelCT isa (fun s t => CrtScopedInput g bs1 s ∧ CrtScopedInput g bs2 t ∧ s.sp = t.sp)
      (CrtFn.bodyWith kernel.code) (fun _ _ => True) := by
  intro s t tr1 tr2 u v h e1 e2
  obtain ⟨trS, uS, runS, _⟩ := (crt_body_ok (kernel := kernel)) _ h.1.body
  obtain ⟨trT, uT, runT, _⟩ := (crt_body_ok (kernel := kernel)) _ h.2.1.body
  obtain ⟨writeS, readS⟩ := crt_expanded_covers h.1.workspace h.1.body.buffers.storageFits
  obtain ⟨writeT, readT⟩ := crt_expanded_covers h.2.1.workspace h.2.1.body.buffers.storageFits
  have wideS : Exec isa (CrtFn.bodyWith kernel.code) s trS (uS.withRegions s.rd s.wr) := by
    simpa only [crtExpanded, State.withRegions_withRegions, State.withRegions_self] using VG.Arm.Exec.widen runS readS writeS
  have wideT : Exec isa (CrtFn.bodyWith kernel.code) t trT (uT.withRegions t.rd t.wr) := by
    simpa only [crtExpanded, State.withRegions_withRegions, State.withRegions_self] using VG.Arm.Exec.widen runT readT writeT
  have trace := (crt_body_ct (kernel := kernel)) modulus _ _ _ _ _ _ ⟨h.1.body, h.2.1.body, h.2.2⟩ runS runT
  exact ⟨(Exec.det e1 wideS).1.trans (trace.1.trans (Exec.det e2 wideT).1.symm), trivial⟩

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtEntry.lean`, which only this module imported.
section

/-! # Save private RSA output and scratch pointers in the call frame -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest Upd wp_str wp_mov op2_reg)

theorem crt_entry_ok (s : State) {base : BitVec 32}
    (fit : s.sp.toNat + 108 ≤ 2 ^ 32)
    (stack : (⟨State.addr s.sp, 56⟩ : Region) ∈ s.wr)
    (argRead : InRegions (s.rd ++ s.wr) (off (State.addr s.sp) 104) 4)
    (arg : s.mem.readW (off (State.addr s.sp) 104) 32 = base) :
    WP isa (.block CrtFn.entry) s fun t =>
      t.gpr .r0 = base ∧ t.gpr .r4 = s.gpr .r2 ∧ t.gpr .r6 = s.gpr .r3 ∧
      t.mem = (s.mem.writeW (off (State.addr s.sp) 4) (s.gpr .r0)).writeW (State.addr s.sp) base ∧
      Rest [.r0, .r4, .r6, .r12] s t := by
  unfold CrtFn.entry
  refine wp_stackAddr (by decide) fun u h => ?_
  have ptr : u.gpr .r12 = s.sp := by simpa only [BitVec.add_zero] using h.gpr
  refine wp_str (a := off (State.addr s.sp) 4) (by decide)
    (by rw [ptr]; exact addr_add (by omega))
    (by rw [h.wr]; exact ⟨_, stack, Offset.contains_base _ (by decide) (by decide)⟩) fun v j => ?_
  have outside := writeW32_outside s.mem (State.addr s.sp) (d := 4) (s.gpr .r0) (by decide)
  have memV : v.mem = s.mem.writeW (off (State.addr s.sp) 4) (s.gpr .r0) := by
    rw [j.mem, h.mem, h.other .r0 (by decide)]
  have argV : v.mem.readW (off (State.addr s.sp) 104) 32 = base := by
    rw [memV, outside_read32 outside (by decide) (by decide)]; exact arg
  refine wp_loadStack (a := off (State.addr s.sp) 104) (by decide)
    (by rw [j.sp, h.sp]; exact addr_add (by omega))
    (by rw [j.rd, j.wr, h.rd, h.wr]; exact argRead) fun z l => ?_
  have baseZ : z.gpr .r0 = base := l.gpr.trans argV
  refine wp_str (a := State.addr s.sp) (by decide)
    (by rw [l.other .r12 (by decide), j.gpr, ptr]; simp)
    (by rw [l.wr, j.wr, h.wr]; exact ⟨_, stack, by simp [Region.Contains]⟩) fun a q => ?_
  refine wp_mov (op2_reg _ _) fun b r => ?_
  refine wp_mov (op2_reg _ _) fun t f => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [f.other .r0 (by decide), r.other .r0 (by decide), q.gpr, baseZ]
  · rw [f.other .r4 (by decide), r.gpr, q.gpr, l.other .r2 (by decide), j.gpr, h.other .r2 (by decide)]
  · rw [f.gpr, r.other .r3 (by decide), q.gpr, l.other .r3 (by decide), j.gpr, h.other .r3 (by decide)]
  · rw [f.mem, r.mem, q.mem, baseZ, l.mem, memV]
  · exact (h.rest (by simp)).trans ((j.rest _).trans ((l.rest (by simp)).trans
      ((q.rest _).trans ((r.rest (by simp)).trans (f.rest (by simp))))))

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtEntryBuffers.lean`, which only this module imported.
section

/-! # Stack entry preserves all source bytes and provides the three scratch subworkspaces -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem crtExpanded_read {s : State} {base : BitVec 32} {w n : Nat} {a : Addr}
    (h : InRegions (s.rd ++ s.wr) a n) : InRegions ((crtExpanded s base w).rd ++ (crtExpanded s base w).wr) a n := by
  obtain ⟨r, hr, hc⟩ := h
  refine ⟨r, ?_, hc⟩
  simp only [crtExpanded, State.withRegions, List.mem_append] at hr ⊢
  rcases hr with hr | hr
  · exact Or.inl hr
  · exact Or.inr (Or.inr hr)

theorem crtExpanded_write {s : State} {base : BitVec 32} {w n : Nat} {a : Addr}
    (h : InRegions s.wr a n) : InRegions (crtExpanded s base w).wr a n := by
  obtain ⟨r, hr, hc⟩ := h
  exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem crt_entry_buffers {s t : State} {g : CrtGeometry} {bs : Fin 7 → List Byte} {rs : List Reg}
    (h : CrtFnInput g bs s) (frame : Frame [FrameStack.belowA s.sp 56] s.mem t.mem)
    (rest : Rest rs (pcPushed s) t) : CrtBuffers g bs (crtExpanded t g.base g.words) := by
  have ws : Workspace t g.base g.size :=
    ⟨h.workspace.nowrap, by rw [rest.wr]; exact List.mem_cons_of_mem _ h.workspace.writable⟩
  have width := crt_width_valid h.lengthValid
  have source (i : Fin 7) : PublicBytes (g.source i) (g.sourceLength i) (bs i) (crtExpanded t g.base g.words) := by
    refine ⟨(h.source i).fits, crtExpanded_read ?_, ?_⟩
    · rw [rest.rd, rest.wr]
      exact InRegions_append_cons.mpr (Or.inr (h.source i).read)
    · exact (rsa_bytes_frame frame (by have := (h.source i).fits; omega)
        (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact (h.stackSource i).symm)).trans (h.source i).bytes
  refine ⟨⟨ws.nowrap, List.mem_append_right _ ws.writable⟩,
    crt_expanded_context ws h.storageFits width.1 (by have := width.2.1; change Spec.Rsa.modulusWords g.length < _; omega), h.lengthValid,
    h.storageFits, h.pPositive, h.pShort, h.qPositive, h.qShort, source, h.sourceSeparate,
    ?_, h.outputFits, crtExpanded_write ?_, h.outputSeparate, ?_⟩
  · intro i
    change Region.Disjoint _ ⟨State.addr t.sp, 56⟩
    rw [rest.sp]; exact (h.stackSource i).symm
  · rw [rest.wr]
    obtain ⟨r, hr, hc⟩ := h.write
    exact ⟨r, List.mem_cons_of_mem _ hr, hc⟩
  · change Region.Disjoint _ ⟨State.addr t.sp, 56⟩
    rw [rest.sp]; exact h.stackOutput.symm

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtPush.lean`, which only this module imported.
section

/-! # Geometry and input preservation across the private RSA stack push -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont

theorem crt_push_arguments {s : State} {g : CrtGeometry} {bs : Fin 7 → List Byte} (h : CrtFnInput g bs s) :
    InRegions ((pcPushed s).rd ++ (pcPushed s).wr) (off (State.addr (pcPushed s).sp) 56) 56 ∧
      WorkspaceEq (State.addr s.sp) 56 s.mem (pcPushed s).mem := by
  have frame := FrameStack.pushed_frameA
    (rs := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]) h.stackFit
  refine ⟨?_, WorkspaceEq.of_frame (by decide) frame ?_⟩
  · rw [public_push_argAddr h.stackFit]
    exact InRegions_append_cons.mpr (Or.inr h.argRead)
  · intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.stackArgs.symm

theorem crt_push_separate {s : State} {g : CrtGeometry} {bs : Fin 7 → List Byte} (h : CrtFnInput g bs s) :
    (⟨State.addr (pcPushed s).sp, 112⟩ : Region).Disjoint ⟨State.addr g.base, g.size⟩ := by
  intro a ha hb
  have lo : (⟨State.addr (pcPushed s).sp, 56⟩ : Region).Disjoint ⟨State.addr g.base, g.size⟩ := h.stackWorkspace
  by_cases low : (a - State.addr (pcPushed s).sp).toNat < 56
  · exact lo a low hb
  · apply h.argsWorkspace a ?_ hb
    rw [← public_push_argAddr h.stackFit]
    change (a - (State.addr (pcPushed s).sp + BitVec.ofNat 64 56)).toNat + 1 ≤ 56
    have inside := (Offset.lt_iff a (State.addr (pcPushed s).sp) (d := 56) (n := 56) (by decide)).mpr
      ⟨by omega, by change (a - State.addr (pcPushed s).sp).toNat + 1 ≤ 112 at ha; omega⟩
    omega

end VG.Proof.Bignum.Arm
end

end

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem crt_entry_ready (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} (h : CrtFnInput g bs s) :
    WP isa (.block CrtFn.entry) (pcPushed s) fun t => CrtScopedInput g bs t ∧
      Frame [FrameStack.belowA s.sp 56] s.mem t.mem ∧
      Spill.Saved t.mem (State.addr t.sp) s.gpr pcCalleeSaved ∧ Rest roundClobbers (pcPushed s) t := by
  have pushFrame := FrameStack.pushed_frameA
    (rs := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]) h.stackFit
  have spNat : (pcPushed s).sp.toNat = s.sp.toNat - 56 := FrameStack.sub_toNat' h.stackFit
  obtain ⟨argRead, argEq⟩ := crt_push_arguments h
  have argOffset (d : Nat) : VG.Proof.Mont.off (State.addr (pcPushed s).sp) (56 + d) = VG.Proof.Mont.off (State.addr s.sp) d :=
    public_push_argOffset h.stackFit d
  have readBase := CallLay.inRegions_sub (off := 48) argRead (l := 4) (by decide) (by decide)
  rw [show off (State.addr (pcPushed s).sp) 56 + BitVec.ofNat 64 48 = off (State.addr (pcPushed s).sp) 104
    from Offset.add_add _ 56 48] at readBase
  have baseArg : (pcPushed s).mem.readW (off (State.addr (pcPushed s).sp) 104) 32 = g.base := by
    rw [public_push_argOffset h.stackFit 48, argEq.word (d := 48) (bits := 32) (by decide)]
    exact h.workspaceArg
  refine WP.mono (crt_entry_ok (pcPushed s) (by rw [spNat]; have := h.argFit; omega)
    (List.mem_cons_self) readBase baseArg) ?_
  rintro t ⟨ptr, source, count, mem, rest⟩
  obtain ⟨savedBase, savedOutput, outside, frameEntry⟩ := pcEntry_memory mem
  have frameEntryFull : Frame [FrameStack.belowA s.sp 56] (pcPushed s).mem t.mem :=
    frameEntry.sub (by intro r hr; simp only [List.mem_singleton] at hr; subst r
                       exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩)
  have frame := pushFrame.trans frameEntryFull
  have savedAll := pc_push_saved s h.stackFit
  have savedCallee := pcEntry_callee_saved (pc_push_callee_saved s h.stackFit) mem
  have stack : CrtCallStack g (crtExpanded t g.base g.words) := by
    refine ⟨?_, crtExpanded_read ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · change t.sp.toNat + 112 ≤ _
      rw [rest.sp, spNat]; have := h.argFit; omega
    · change InRegions (t.rd ++ t.wr) (VG.Proof.Mont.off (State.addr t.sp) 56) 56
      rw [rest.rd, rest.wr, rest.sp]; exact argRead
    · change (⟨State.addr t.sp, 56⟩ : Region) ∈ _ ++ t.wr
      rw [rest.wr, rest.sp]
      exact List.mem_append_right _ List.mem_cons_self
    · change Region.Disjoint ⟨State.addr t.sp, 112⟩ _
      rw [rest.sp]; exact crt_push_separate h
    · change t.mem.readW (off (State.addr t.sp) 4) 32 = _
      rw [rest.sp]; exact savedOutput.trans h.output
    · change t.mem.readW (off (State.addr t.sp) 12) 32 = _
      rw [rest.sp, outside_read32 outside (d := 12) (by decide) (by decide)]
      exact (savedAll (.r3, 12) (by decide)).trans h.count
    · intro i
      change t.mem.readW (off (State.addr t.sp) (56 + 8 * i.val)) 32 = _
      rw [rest.sp, outside_read32 outside (d := 56 + 8 * i.val) (by omega) (by have := i.isLt; omega),
        argOffset (8 * i.val), argEq.word (d := 8 * i.val) (bits := 32) (by have := i.isLt; omega)]
      exact h.pointer i
    · intro i
      change t.mem.readW (off (State.addr t.sp) (60 + 8 * i.val)) 32 = _
      rw [rest.sp, outside_read32 outside (d := 60 + 8 * i.val) (by omega) (by have := i.isLt; omega),
        show 60 + 8 * i.val = 56 + (4 + 8 * i.val) by omega,
        argOffset (4 + 8 * i.val), argEq.word (d := 4 + 8 * i.val) (bits := 32) (by have := i.isLt; omega)]
      exact h.length i
  refine ⟨⟨⟨h.workspace.nowrap, by rw [rest.wr]; exact List.mem_cons_of_mem _ h.workspace.writable⟩,
    ⟨crt_entry_buffers h frame rest, stack, ptr, source.trans h.modulus, count.trans h.count, ?_, ?_⟩⟩,
    frame, ?_, rest.mono (by decide)⟩
  · change t.mem.readW (State.addr t.sp) 32 = _
    rw [rest.sp]; exact savedBase
  · change t.mem.readW (off (State.addr t.sp) 8) 32 = _
    rw [rest.sp, outside_read32 outside (d := 8) (by decide) (by decide)]
    exact (savedAll (.r2, 8) (by decide)).trans h.modulus
  · rw [rest.sp]; exact savedCallee

end VG.Proof.Bignum.Arm
