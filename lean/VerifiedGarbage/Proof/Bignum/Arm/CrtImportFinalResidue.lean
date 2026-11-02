module
public import VerifiedGarbage.Impl.Bignum.Arm.CrtFn
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Proof.Bignum.Arm.SanitizeModulusCT
public import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedState

import VerifiedGarbage.Proof.Bignum.Arm.CrtQSource
import VerifiedGarbage.Proof.Bignum.Arm.TransferArray
import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedWorkspace
import VerifiedGarbage.Proof.Bignum.Arm.LayoutFrameReady
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Framework.Block

/-! # Copy the final q residue into the main reconstruction workspace -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt Operand)
open VG.Proof.X25519.Arm (Rest)

theorem crt_importFinalResidue_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtShared g bs s) (ready : LayoutFrameReady g.base (workspaceWords g.words) g.words s) :
    WP isa (.seq (.block CrtFn.qSource) (transferArray 1 6)) s fun t =>
      CrtShared g bs t ∧ LayoutFrameReady g.base (workspaceWords g.words) g.words t ∧
      numAt t.mem (State.addr g.base) g.words 1 = numAt s.mem (State.addr (crtQ g.base g.words)) g.words 6 ∧
      Frame [⟨State.addr g.base, 8 * workspaceWords g.words⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [WP.seq_iff]
  refine WP.mono (crt_qSource_ok s h) ?_
  rintro u ⟨qptr, memU, restU⟩
  have sharedU := h.of_mem memU restU
  have readyU := ready.of_mem memU restU ((restU.gpr .r0 (by decide)).trans ready.ptr)
  have input : TransferArrayInput g.base (crtQ g.base g.words)
      (workspaceWords g.words) (workspaceWords g.words) g.words u :=
    ⟨readyU, sharedU.buffers.context.q, sharedU.q, qptr, h.buffers.context.sepMQ.symm⟩
  refine WP.mono (transferArray_ok u input (by decide : 1 < 8) (by decide : 6 < 8)) ?_
  rintro t ⟨readyT, value, keeps, frame, rest⟩
  have header (d : Nat) (hd : d + 4 ≤ 256) :
      t.mem.readW (off (State.addr g.base) d) 32 = u.mem.readW (off (State.addr g.base) d) 32 :=
    keeps_header_readW keeps sharedU.main.toCrtLayoutState.size hd
  have mainT : CrtMainState g.base (workspaceWords g.words) g.words t.mem :=
    ⟨⟨readyT.layout, readyT.width⟩, (header 224 (by decide)).trans sharedU.main.p,
      (header 228 (by decide)).trans sharedU.main.q, (header 232 (by decide)).trans sharedU.main.product,
      (header 236 (by decide)).trans sharedU.main.compare, (header 240 (by decide)).trans sharedU.main.modulus⟩
  have modulus := keeps_array_num keeps h.buffers.context.arraysFit
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp] : Operand 0) (by decide : 0 ≠ 1)
  have sharedT := sharedU.after_main (frame.mono (by simp)) rest mainT modulus
  rw [memU] at value frame
  exact ⟨sharedT, readyT, value, frame, (restU.mono (by decide)).trans rest⟩

end VG.Proof.Bignum.Arm
