module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtImportQResidue
public import VerifiedGarbage.Proof.Bignum.Arm.CrtCoefficient
public import VerifiedGarbage.Proof.Bignum.Arm.CrtSavedSources
public import VerifiedGarbage.Proof.Bignum.Arm.CrtSelectWorkspace
public import VerifiedGarbage.Proof.Bignum.Arm.CrtBothPowers
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Complete coefficient phase with stable q residue and acceptance bit -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Spec.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

theorem crt_coefficientStage_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} {P Q v1 v2 : Nat}
    (h : CrtShared g bs s) (ready : LayoutFrameReady g.base (workspaceWords g.words) g.words s)
    (p : CrtPoweredState (crtP g.base g.words) (workspaceWords g.words) g.words P v1 s.mem)
    (q : CrtPoweredState (crtQ g.base g.words) (workspaceWords g.words) g.words Q v2 s.mem)
    (odd : P % 2 = 1) (bound : v1 < P) :
    WP isa CrtFn.coefficientPhase s fun t => CrtShared g bs t ∧
      LayoutFrameReady g.base (workspaceWords g.words) g.words t ∧
      numAt t.mem (State.addr (crtP g.base g.words)) g.words 0 = P ∧
      numAt t.mem (State.addr (crtP g.base g.words)) g.words 5 =
        ((((v1 : Int) - v2) * Spec.Rsa.os2ip (bs 6)) % (P : Int)).toNat ∧
      CrtPoweredState (crtQ g.base g.words) (workspaceWords g.words) g.words Q v2 t.mem ∧
      t.mem.readW (off (State.addr t.sp) 48) 32 = s.mem.readW (off (State.addr s.sp) 48) 32 ∧
      Frame (crtLiveMutable g s.sp) s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [CrtFn.coefficientPhase, WP.seq_iff]
  refine WP.mono (crt_selectLinked_ready s h h.buffers.context.p h.p (by simp [crtRegions])
    (by have := h.buffers.context.size; omega : 224 + 4 ≤ 8 * workspaceWords g.words)
    (by decide) ready.ptr h.main.p) ?_
  rintro u ⟨sharedU, readyU, frameU, restU⟩
  have pEqU := h.workspace_eq_after_base h.buffers.context.p (by simp [crtRegions]) frameU
  have qEqU := h.workspace_eq_after_base h.buffers.context.q (by simp [crtRegions]) frameU
  have pU := p.congr pEqU
  have qU := q.congr qEqU
  apply WP.assoc
  rw [WP.seq_iff]
  refine WP.mono (crt_importQResidue_ok u sharedU readyU pU) ?_
  rintro v ⟨sharedV, readyV, pV, residue, frameV, restV⟩
  have input : CrtCoefficientInput (crtP g.base g.words) g.qi (workspaceWords g.words) g.words g.pLength P (bs 6) v :=
    ⟨⟨pV.ready readyV, pV.modulus, odd, pV.r2, pV.one, by rw [pV.result]; exact bound⟩,
      sharedV.savedOperand 5 (by simp [crtRegions]), h.buffers.pPositive,
      by have := h.buffers.pShort; have := (crt_width_valid h.buffers.lengthValid).2.2
         change _ ≤ 8 * Spec.Rsa.modulusWords g.length; omega⟩
  rw [WP.seq_iff]
  refine WP.mono (crt_coefficient_ok v input) ?_
  rintro x ⟨arithmetic, modulus, value, frameX, restX⟩
  rw [pV.result, residue, qU.result] at value
  have sharedX := sharedV.after_p (frameX.mono (by simp)) restX ⟨arithmetic.layout, arithmetic.width⟩
  refine WP.mono (crt_selectMain_ready x sharedX) ?_
  rintro t ⟨sharedT, readyT, frameT, restT⟩
  have pEqT := sharedX.workspace_eq_after_base arithmetic.workspace (by simp [crtRegions]) frameT
  have qEqV := sharedU.workspace_eq_after sharedU.buffers.context.q (by simp [crtRegions]) sharedU.buffers.context.sepPQ.symm (frameV.mono (by simp))
  have qEqX := sharedV.workspace_eq_after sharedV.buffers.context.q (by simp [crtRegions]) sharedV.buffers.context.sepPQ.symm (frameX.mono (by simp))
  have qEqT := sharedX.workspace_eq_after_base sharedX.buffers.context.q (by simp [crtRegions]) frameT
  have flag := (acceptance_after_base_save frameT restT).trans
    ((sharedV.acceptance_after_workspace (by simp [crtRegions]) frameX restX).trans
      ((sharedU.acceptance_after_workspace (by simp [crtRegions]) frameV restV).trans (acceptance_after_base_save frameU restU)))
  have frameVLive := crt_workspace_frame (child := crtP g.base g.words) sharedU.buffers.workspace sharedU.buffers.storageFits (by simp [crtRegions]) (frameV.mono (by simp))
  have frameXLive := crt_workspace_frame (child := crtP g.base g.words) sharedV.buffers.workspace sharedV.buffers.storageFits (by simp [crtRegions]) (frameX.mono (by simp))
  rw [restU.sp] at frameVLive
  rw [restV.sp, restU.sp] at frameXLive
  rw [restX.sp, restV.sp, restU.sp] at frameT
  exact ⟨sharedT, readyT, (pEqT.number h.buffers.context.arraysFit (by decide)).trans modulus,
    (pEqT.number h.buffers.context.arraysFit (by decide)).trans value,
    ((qU.congr qEqV).congr qEqX).congr qEqT, flag,
    (frameU.mono (by simp [crtLiveMutable])).trans (frameVLive.trans (frameXLive.trans (frameT.mono (by simp [crtLiveMutable])))),
    (restU.mono (by simp [roundClobbers])).trans (restV.trans (restX.trans (restT.mono (by simp [roundClobbers]))))⟩

end VG.Proof.Bignum.Arm
