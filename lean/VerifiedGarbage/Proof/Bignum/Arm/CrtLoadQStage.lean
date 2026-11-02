module

public import VerifiedGarbage.Impl.Bignum.Arm.CrtFn
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Proof.Bignum.Arm.SanitizeModulusCT
public import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedFrame
import VerifiedGarbage.Proof.Bignum.Arm.CrtSavedSources
import VerifiedGarbage.Proof.Bignum.Arm.CrtSelectWorkspace
import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedWorkspace
import VerifiedGarbage.Proof.Bignum.Arm.SavedOperandLayout
import VerifiedGarbage.Proof.Bignum.Arm.CrtLayout
import VerifiedGarbage.Proof.Framework.Block

/-! # Import q while preserving p and the accumulated secret acceptance bit -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

theorem crt_loadQStage_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtShared g bs s) (ready : LayoutFrameReady g.base (workspaceWords g.words) g.words s) :
    WP isa CrtFn.loadQ s fun t => CrtShared g bs t ∧
      LayoutFrameReady g.base (workspaceWords g.words) g.words t ∧
      numAt t.mem (State.addr (crtP g.base g.words)) g.words 0 = numAt s.mem (State.addr (crtP g.base g.words)) g.words 0 ∧
      numAt t.mem (State.addr (crtQ g.base g.words)) g.words 0 = Spec.Rsa.os2ip (bs 3) ∧
      t.mem.readW (off (State.addr t.sp) 48) 32 = s.mem.readW (off (State.addr s.sp) 48) 32 ∧
      Frame (crtLiveMutable g s.sp) s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [CrtFn.loadQ, WP.seq_iff]
  refine WP.mono (crt_selectLinked_ready s h h.buffers.context.q h.q (by simp [crtRegions])
    (by have := h.buffers.context.size; omega : 228 + 4 ≤ 8 * workspaceWords g.words)
    (by decide) ready.ptr h.main.q) ?_
  rintro u ⟨sharedU, readyU, frameU, restU⟩
  have source : SavedOperand (crtQ g.base g.words) g.q (workspaceWords g.words) g.qLength 72 76 (bs 3) u :=
    sharedU.savedOperand 2 (by simp [crtRegions])
  rw [WP.seq_iff]
  refine WP.mono (savedOperandLayout_ok u readyU source (by decide : 0 < 8) h.buffers.qPositive
    (by have := (crt_width_valid h.buffers.lengthValid).2.2; have := h.buffers.qShort; change _ ≤ 8 * Spec.Rsa.modulusWords g.length; omega)) ?_
  rintro v ⟨readyV, value, _, frameV, restV⟩
  have frameV' : Frame [⟨State.addr (crtQ g.base g.words), 8 * workspaceWords g.words⟩,
      ⟨off (State.addr u.sp) 48, 4⟩] u.mem v.mem := frameV.mono (by simp)
  have sharedV := sharedU.after_q frameV' restV ⟨readyV.layout, readyV.width⟩
  refine WP.mono (crt_selectMain_ready v sharedV) ?_
  rintro t ⟨sharedT, readyT, frameT, restT⟩
  have eqU := h.workspace_eq_after_base h.buffers.context.p (by simp [crtRegions]) frameU
  have eqV := sharedU.workspace_eq_after sharedU.buffers.context.p (by simp [crtRegions]) sharedU.buffers.context.sepPQ frameV'
  have eqT := sharedV.workspace_eq_after_base sharedV.buffers.context.p (by simp [crtRegions]) frameT
  have eqQ := sharedV.workspace_eq_after_base readyV.workspace (by simp [crtRegions]) frameT
  have prime := (eqT.number h.buffers.context.arraysFit (by decide : 0 < 8)).trans
    ((eqV.number h.buffers.context.arraysFit (by decide : 0 < 8)).trans (eqU.number h.buffers.context.arraysFit (by decide : 0 < 8)))
  have flag := (acceptance_after_base_save frameT restT).trans
    ((sharedU.acceptance_after_workspace (by simp [crtRegions]) frameV restV).trans (acceptance_after_base_save frameU restU))
  have frameVLive := crt_workspace_frame sharedU.buffers.workspace sharedU.buffers.storageFits (by simp [crtRegions]) frameV'
  rw [restU.sp] at frameVLive
  have restUV : Rest roundClobbers s v := (restU.mono (by decide)).trans restV
  rw [restUV.sp] at frameT
  exact ⟨sharedT, readyT, prime, (eqQ.number h.buffers.context.arraysFit (by decide : 0 < 8)).trans value, flag,
    (frameU.mono (by simp [crtLiveMutable])).trans (frameVLive.trans (frameT.mono (by simp [crtLiveMutable]))),
    restUV.trans (restT.mono (by decide))⟩

end VG.Proof.Bignum.Arm
