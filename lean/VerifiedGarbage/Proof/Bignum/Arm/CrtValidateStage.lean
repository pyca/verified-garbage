module

public import VerifiedGarbage.Impl.Bignum.Arm.CrtFn
public import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedFrame
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Proof.Bignum.Arm.SanitizeModulusCT

import VerifiedGarbage.Proof.Bignum.Arm.CrtAcceptStage
import VerifiedGarbage.Proof.Bignum.Arm.CrtLoadPStage
import VerifiedGarbage.Proof.Bignum.Arm.CrtLoadQStage
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Impl.Bignum.Arm.CrtValidateProduct
import VerifiedGarbage.Impl.Bignum.Arm.MergeAcceptance
import VerifiedGarbage.Proof.Bignum.Arm.CrtValidationPreserved
import VerifiedGarbage.Proof.Bignum.Arm.CrtProductValues
import VerifiedGarbage.Proof.Bignum.Arm.MergeAcceptanceLayout
import VerifiedGarbage.Proof.Bignum.Arm.CrtValidationGeometry
import VerifiedGarbage.Proof.Bignum.Arm.CrtStorage
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
import VerifiedGarbage.Proof.Framework.Offset
/-! # Exact acceptance and imported factors for the private RSA computation -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtProductStage.lean`, which only this module imported.
section

/-! # Accumulate the exact factor-product validation bit -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

theorem crt_productStage_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtShared g bs s) (ready : LayoutFrameReady g.base (workspaceWords g.words) g.words s) :
    WP isa (.seq validateProduct (.block mergeAcceptance)) s fun t => CrtShared g bs t ∧
      LayoutFrameReady g.base (workspaceWords g.words) g.words t ∧
      numAt t.mem (State.addr (crtP g.base g.words)) g.words 0 = numAt s.mem (State.addr (crtP g.base g.words)) g.words 0 ∧
      numAt t.mem (State.addr (crtQ g.base g.words)) g.words 0 = numAt s.mem (State.addr (crtQ g.base g.words)) g.words 0 ∧
      t.mem.readW (off (State.addr t.sp) 48) 32 =
        (if numAt s.mem (State.addr (crtP g.base g.words)) g.words 0 *
          numAt s.mem (State.addr (crtQ g.base g.words)) g.words 0 = Spec.Rsa.os2ip (bs 0) then 1 else 0) &&&
        s.mem.readW (off (State.addr s.sp) 48) 32 ∧
      Frame (crtLiveMutable g s.sp) s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [WP.seq_iff]
  refine WP.mono (crt_validateProduct_ok s (h.validate_input ready)) ?_
  rintro u ⟨value, outside, frame, ptr, rest⟩
  have sharedU := h.after_validation outside frame rest
  have readyU : LayoutFrameReady g.base (workspaceWords g.words) g.words u :=
    ⟨⟨sharedU.buffers.context.main, sharedU.main.layout, sharedU.main.width, ptr⟩,
      by rw [rest.rd, rest.wr, rest.sp]; exact ready.stackRead,
      by rw [rest.sp]; exact ready.stackSep,
      saved_base_kept frame (h.stack.separate.sub_left (Region.sub_prefix (by decide))) ready.saved rest.sp⟩
  have stackEq : WorkspaceEq (State.addr s.sp) 112 s.mem u.mem := WorkspaceEq.of_frame (by decide) frame (by
    intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.stack.separate)
  have flagU : u.mem.readW (off (State.addr u.sp) 48) 32 = s.mem.readW (off (State.addr s.sp) 48) 32 := by
    rw [rest.sp]; exact stackEq.word (by decide)
  obtain ⟨pEq, qEq⟩ := h.validation_child_eq outside
  obtain ⟨pValue, qValue⟩ := h.product_values false
  rw [pValue, qValue, h.modulus] at value
  refine WP.mono (mergeAcceptanceLayout_ready u readyU (by have := sharedU.stack.nowrap; omega)
    (sharedU.stack.write (by decide))
    ((sharedU.stack.separate.symm.sub_left (crt_region_sub_workspace sharedU.buffers.workspace sharedU.buffers.storageFits
      (by simp [crtRegions]))).sub_right (Offset.sub_base _ (by decide)))) ?_
  rintro t ⟨readyT, flagT, _, frameT, restT, _⟩
  have separate : ∀ r ∈ [⟨off (State.addr u.sp) 48, 4⟩], (⟨State.addr g.base, g.size⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst r
    exact sharedU.stack.separate.symm.sub_right (Offset.sub_base _ (by decide))
  have sharedT := sharedU.after_external frameT restT (by simp [crtLiveMutable]) separate
  have eqChild (child : BitVec 32) (ws : Workspace u child (8 * workspaceWords g.words))
      (member : (⟨State.addr child, 8 * workspaceWords g.words⟩ : Region) ∈ crtRegions g.base (workspaceWords g.words) g.words) :
      WorkspaceEq (State.addr child) (8 * workspaceWords g.words) u.mem t.mem :=
    WorkspaceEq.of_frame (by have := ws.nowrap; omega) frameT
      (fun r hr => (separate r hr).sub_left (crt_region_sub_workspace sharedU.buffers.workspace sharedU.buffers.storageFits member))
  rw [value, flagU] at flagT
  have frameTLive := frameT.mono (show ∀ r ∈ [⟨off (State.addr u.sp) 48, 4⟩], r ∈ crtLiveMutable g u.sp by simp [crtLiveMutable])
  rw [rest.sp] at frameTLive
  exact ⟨sharedT, readyT,
    ((eqChild _ sharedU.buffers.context.p (by simp [crtRegions])).number h.buffers.context.arraysFit (by decide)).trans
      (pEq.number h.buffers.context.arraysFit (by decide)),
    ((eqChild _ sharedU.buffers.context.q (by simp [crtRegions])).number h.buffers.context.arraysFit (by decide)).trans
      (qEq.number h.buffers.context.arraysFit (by decide)), flagT,
    (frame.mono (by simp [crtLiveMutable])).trans frameTLive,
    rest.trans (restT.mono (by decide))⟩

end VG.Proof.Bignum.Arm
end

end

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

def crtAccepted (bs : Fin 7 → List Byte) : Prop :=
  Spec.Rsa.os2ip (bs 1) < Spec.Rsa.os2ip (bs 0) ∧
  Spec.Rsa.os2ip (bs 6) < Spec.Rsa.os2ip (bs 2) ∧
  Spec.Rsa.os2ip (bs 2) * Spec.Rsa.os2ip (bs 3) = Spec.Rsa.os2ip (bs 0)
instance (bs : Fin 7 → List Byte) : Decidable (crtAccepted bs) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem crt_validateStage_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtShared g bs s) (ready : LayoutFrameReady g.base (workspaceWords g.words) g.words s) :
    WP isa CrtFn.validate s fun t => CrtShared g bs t ∧
      LayoutFrameReady g.base (workspaceWords g.words) g.words t ∧
      numAt t.mem (State.addr (crtP g.base g.words)) g.words 0 = Spec.Rsa.os2ip (bs 2) ∧
      numAt t.mem (State.addr (crtQ g.base g.words)) g.words 0 = Spec.Rsa.os2ip (bs 3) ∧
      t.mem.readW (off (State.addr t.sp) 48) 32 = (if crtAccepted bs then 1 else 0) ∧
      Frame (crtLiveMutable g s.sp) s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [CrtFn.validate, WP.seq_iff]
  refine WP.mono (crt_acceptStage_ok s h ready) ?_
  rintro u ⟨sharedU, readyU, flagU, frameU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (crt_loadPStage_ok u sharedU readyU) ?_
  rintro v ⟨sharedV, readyV, pV, _, flagV, frameV, restV⟩
  rw [WP.seq_iff]
  refine WP.mono (crt_loadQStage_ok v sharedV readyV) ?_
  rintro x ⟨sharedX, readyX, pX, qX, flagX, frameX, restX⟩
  refine WP.mono (crt_productStage_ok x sharedX readyX) ?_
  rintro t ⟨sharedT, readyT, pT, qT, flagT, frameT, restT⟩
  rw [pX, pV, qX, flagX, flagV, flagU] at flagT
  have flag : t.mem.readW (off (State.addr t.sp) 48) 32 = (if crtAccepted bs then 1 else 0) := by
    rw [flagT]
    by_cases hx : Spec.Rsa.os2ip (bs 1) < Spec.Rsa.os2ip (bs 0) <;>
      by_cases hi : Spec.Rsa.os2ip (bs 6) < Spec.Rsa.os2ip (bs 2) <;>
      by_cases hp : Spec.Rsa.os2ip (bs 2) * Spec.Rsa.os2ip (bs 3) = Spec.Rsa.os2ip (bs 0) <;>
      simp [crtAccepted, hx, hi, hp]
  rw [restU.sp] at frameV
  rw [restV.sp, restU.sp] at frameX
  rw [restX.sp, restV.sp, restU.sp] at frameT
  exact ⟨sharedT, readyT, pT.trans (pX.trans pV), qT.trans qX, flag,
    frameU.trans (frameV.trans (frameX.trans frameT)), restU.trans (restV.trans (restX.trans restT))⟩

end VG.Proof.Bignum.Arm
