module

public import VerifiedGarbage.Impl.Bignum.Arm.CrtFn
public import VerifiedGarbage.Proof.Bignum.Arm.CrtPoweredState
public import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedState

import VerifiedGarbage.Proof.Bignum.Arm.CrtQSource
import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedWorkspace
import VerifiedGarbage.Proof.Bignum.Arm.TransferArray
import VerifiedGarbage.Proof.Bignum.Arm.LayoutFrameReady
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
/-! # Transfer the q residue to p while retaining p's completed arithmetic state -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtPoweredTransfer.lean`, which only this module imported.
section

/-! # Importing the other residue preserves the completed factor power -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt arrAt Operand Keeps)
open VG.Proof.X25519.Arm (Rest)

theorem CrtPoweredState.after_transfer {s t : State} {base : BitVec 32} {len w M value : Nat}
    (h : CrtPoweredState base len w M value s.mem) (selected : LayoutFrameReady base len w s)
    (ptr : t.gpr .r0 = base) (keeps : Keeps (State.addr base) len w 1 s.mem t.mem)
    (frame : Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem) (rest : Rest roundClobbers s t) :
    CrtPoweredState base len w M value t.mem := by
  have fit : arrAt w 8 ≤ 8 * len := h.layout.width ▸ h.layout.layout.2.2.1
  obtain ⟨ready, modulus⟩ := (h.ready selected).after_array (by decide : 1 ≠ 0) keeps frame rest ptr
  have op (j : Nat) (hj : j = 4 ∨ j = 6 ∨ j = 7) : Operand j := by
    rcases hj with rfl | rfl | rfl <;> simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  exact CrtPoweredState.of_ready ready (modulus.trans h.modulus)
    ((keeps_array_num keeps fit (op 6 (by simp)) (by decide)).trans h.result)
    ((keeps_array_num keeps fit (op 4 (by simp)) (by decide)).trans h.r2)
    ((keeps_array_num keeps fit (op 7 (by simp)) (by decide)).trans h.one)

end VG.Proof.Bignum.Arm
end

end

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)
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
  have readyU := ready.of_mem memU restU ((restU.gpr .r0 (by decide)).trans ready.ptr)
  have poweredU : CrtPoweredState (crtP g.base g.words) (workspaceWords g.words) g.words P v u.mem := by rw [memU]; exact powered
  have input : TransferArrayInput (crtP g.base g.words) (crtQ g.base g.words)
      (workspaceWords g.words) (workspaceWords g.words) g.words u :=
    ⟨readyU, sharedU.buffers.context.q, sharedU.q, qptr, h.buffers.context.sepPQ.symm⟩
  refine WP.mono (transferArray_ok u input (by decide : 1 < 8) (by decide : 6 < 8)) ?_
  rintro t ⟨readyT, value, keeps, frame, rest⟩
  have sharedT := sharedU.after_p (frame.mono (by simp)) rest ⟨readyT.layout, readyT.width⟩
  have poweredT := poweredU.after_transfer readyU readyT.ptr keeps frame rest
  rw [memU] at value frame
  exact ⟨sharedT, readyT, poweredT, value, frame, (restU.mono (by decide)).trans rest⟩

end VG.Proof.Bignum.Arm
