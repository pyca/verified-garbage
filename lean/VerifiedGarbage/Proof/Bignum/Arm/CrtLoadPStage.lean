module
public import VerifiedGarbage.Impl.Bignum.Arm.CrtFn
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Proof.Bignum.Arm.SanitizeModulusCT
public import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedFrame

import VerifiedGarbage.Proof.Bignum.Arm.CrtLoadPBody
import VerifiedGarbage.Proof.Bignum.Arm.CrtSavedSources
import VerifiedGarbage.Proof.Bignum.Arm.CrtSelectWorkspace
import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedWorkspace
import VerifiedGarbage.Proof.Bignum.Arm.CrtLayout
import VerifiedGarbage.Proof.Framework.Block

/-! # Complete p and qInv import, validation, and return to the main workspace -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

theorem crt_loadPStage_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtShared g bs s) (ready : LayoutFrameReady g.base (workspaceWords g.words) g.words s) :
    WP isa CrtFn.loadP s fun t => CrtShared g bs t ∧
      LayoutFrameReady g.base (workspaceWords g.words) g.words t ∧
      numAt t.mem (State.addr (crtP g.base g.words)) g.words 0 = Spec.Rsa.os2ip (bs 2) ∧
      numAt t.mem (State.addr (crtP g.base g.words)) g.words 1 = Spec.Rsa.os2ip (bs 6) ∧
      t.mem.readW (off (State.addr t.sp) 48) 32 =
        (if Spec.Rsa.os2ip (bs 6) < Spec.Rsa.os2ip (bs 2) then 1 else 0) &&& s.mem.readW (off (State.addr s.sp) 48) 32 ∧
      Frame (crtLiveMutable g s.sp) s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [CrtFn.loadP, WP.seq_iff]
  refine WP.mono (crt_selectLinked_ready s h h.buffers.context.p h.p (by simp [crtRegions])
    (by have := h.buffers.context.size; omega : 224 + 4 ≤ 8 * workspaceWords g.words)
    (by decide) ready.ptr h.main.p) ?_
  rintro u ⟨sharedU, readyU, frameU, restU⟩
  have input : CrtLoadPInput (crtP g.base g.words) g.p g.qi (workspaceWords g.words) g.words g.pLength (bs 2) (bs 6) u :=
    ⟨readyU, sharedU.savedOperand 1 (by simp [crtRegions]), sharedU.savedOperand 5 (by simp [crtRegions]),
      h.buffers.pPositive,
      by have := (crt_width_valid h.buffers.lengthValid).2.2; have := h.buffers.pShort; change _ ≤ 8 * Spec.Rsa.modulusWords g.length; omega,
      sharedU.stack.write (by decide)⟩
  rw [WP.seq_iff]
  refine WP.mono (crt_loadPBody_ok u input) ?_
  rintro v ⟨readyV, prime, inverse, flag, frameV, restV⟩
  have sharedV := sharedU.after_p frameV restV ⟨readyV.layout, readyV.width⟩
  refine WP.mono (crt_selectMain_ready v sharedV) ?_
  rintro t ⟨sharedT, readyT, frameT, restT⟩
  have eq := sharedV.workspace_eq_after_base readyV.workspace (by simp [crtRegions]) frameT
  have old := acceptance_after_base_save frameU restU
  have flagT := acceptance_after_base_save frameT restT
  rw [flag, old] at flagT
  have frameV' := crt_workspace_frame sharedU.buffers.workspace sharedU.buffers.storageFits (by simp [crtRegions]) frameV
  rw [restU.sp] at frameV'
  have restUV : Rest roundClobbers s v := (restU.mono (by decide)).trans restV
  rw [restUV.sp] at frameT
  exact ⟨sharedT, readyT, (eq.number h.buffers.context.arraysFit (by decide : 0 < 8)).trans prime,
    (eq.number h.buffers.context.arraysFit (by decide : 1 < 8)).trans inverse, flagT,
    (frameU.mono (by simp [crtLiveMutable])).trans (frameV'.trans (frameT.mono (by simp [crtLiveMutable]))),
    restUV.trans (restT.mono (by decide))⟩

end VG.Proof.Bignum.Arm
