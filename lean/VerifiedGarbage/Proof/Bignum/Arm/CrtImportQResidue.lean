module
public import VerifiedGarbage.Impl.Bignum.Arm.CrtFn
public import VerifiedGarbage.Proof.Bignum.Arm.CrtPoweredState
public import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedState

import VerifiedGarbage.Proof.Bignum.Arm.CrtQSource
import VerifiedGarbage.Proof.Bignum.Arm.CrtPoweredTransfer
import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedWorkspace
import VerifiedGarbage.Proof.Bignum.Arm.TransferArray
import VerifiedGarbage.Proof.Bignum.Arm.LayoutFrameReady
import VerifiedGarbage.Proof.Framework.Block

/-! # Transfer the q residue to p while retaining p's completed arithmetic state -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Spec.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

theorem crt_importQResidue_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} {P v : Nat}
    (h : CrtShared g bs s) (ready : LayoutFrameReady (crtP g.base g.words) (workspaceWords g.words) g.words s)
    (powered : CrtPoweredState (crtP g.base g.words) (workspaceWords g.words) g.words P v s.mem) :
    WP isa (.seq (.block CrtFn.qSource) (transferArray 1 6)) s fun t =>
      CrtShared g bs t ∧ LayoutFrameReady (crtP g.base g.words) (workspaceWords g.words) g.words t ∧
      CrtPoweredState (crtP g.base g.words) (workspaceWords g.words) g.words P v t.mem ∧
      numAt t.mem (State.addr (crtP g.base g.words)) g.words 1 = numAt s.mem (State.addr (crtQ g.base g.words)) g.words 6 ∧
      Frame [⟨State.addr (crtP g.base g.words), 8 * workspaceWords g.words⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [WP.seq_iff]
  refine WP.mono (crt_qSource_ok s h) ?_
  rintro u ⟨qptr, memU, restU⟩
  have sharedU := h.of_mem memU restU
  have readyU := ready.of_mem memU restU ((restU.gpr .r0 (by simp)).trans ready.ptr)
  have poweredU : CrtPoweredState (crtP g.base g.words) (workspaceWords g.words) g.words P v u.mem := by rw [memU]; exact powered
  have input : TransferArrayInput (crtP g.base g.words) (crtQ g.base g.words)
      (workspaceWords g.words) (workspaceWords g.words) g.words u :=
    ⟨readyU, sharedU.buffers.context.q, sharedU.q, qptr, h.buffers.context.sepPQ.symm⟩
  refine WP.mono (transferArray_ok u input (by decide : 1 < 8) (by decide : 6 < 8)) ?_
  rintro t ⟨readyT, value, keeps, frame, rest⟩
  have sharedT := sharedU.after_p (frame.mono (by simp)) rest ⟨readyT.layout, readyT.width⟩
  have poweredT := poweredU.after_transfer readyU readyT.ptr keeps frame rest
  rw [memU] at value frame
  exact ⟨sharedT, readyT, poweredT, value, frame, (restU.mono (by simp [roundClobbers])).trans rest⟩

end VG.Proof.Bignum.Arm
