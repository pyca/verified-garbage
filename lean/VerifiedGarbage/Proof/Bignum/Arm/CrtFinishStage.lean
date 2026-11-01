module
public import VerifiedGarbage.Proof.Bignum.Arm.SanitizeModulusCT
public import VerifiedGarbage.Impl.Bignum.Arm.CrtFn
public import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedState
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState

import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Arm.CrtQSource
import VerifiedGarbage.Proof.Bignum.Arm.CrtExportGeometry
import VerifiedGarbage.Proof.Bignum.Arm.CrtRecombineStage
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Reconstruct and export exactly the accepted CRT result, or all zero bytes -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

def crtReconstruction (g : CrtGeometry) (m : Mem) : Nat :=
  numAt m (State.addr (crtP g.base g.words)) g.words 5 *
    numAt m (State.addr (crtQ g.base g.words)) g.words 0 +
    numAt m (State.addr (crtQ g.base g.words)) g.words 6

theorem crt_finishStage_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} {accepted : Bool}
    (h : CrtShared g bs s) (ready : LayoutFrameReady g.base (workspaceWords g.words) g.words s)
    (flag : s.mem.readW (off (State.addr s.sp) 48) 32 = BitVec.ofNat 32 accepted.toNat)
    (bound : accepted = true → crtReconstruction g s.mem < 2 ^ (8 * g.length)) :
    WP isa CrtFn.finish s fun t =>
      Spec.Rsa.bytesAt t.mem (State.addr g.output) g.length =
        (if accepted then Spec.Rsa.i2osp (crtReconstruction g s.mem) g.length else List.replicate g.length 0) ∧
      t.gpr .r0 = BitVec.ofNat 32 accepted.toNat ∧
      Frame [⟨State.addr g.base, g.size⟩, ⟨State.addr g.output, g.length⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  unfold CrtFn.finish
  apply WP.assoc
  apply WP.assoc
  rw [WP.seq_iff]
  refine WP.mono (crt_recombineStage_ok s h ready) ?_
  rintro u ⟨sharedU, readyU, value, frameU, restU⟩
  have stackEq : WorkspaceEq (State.addr s.sp) 112 s.mem u.mem := WorkspaceEq.of_frame (by decide) frameU (by
    intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.stack.separate)
  have flagU : u.mem.readW (off (State.addr u.sp) 48) 32 = BitVec.ofNat 32 accepted.toNat := by
    rw [restU.sp, stackEq.word (d := 48) (bits := 32) (by decide)]; exact flag
  rw [WP.seq_iff]
  refine WP.mono (crt_outputArgs_ok u sharedU readyU.ptr) ?_
  rintro v ⟨source, output, count, memV, restV⟩
  have sharedV := sharedU.of_mem memV restV
  have input := sharedV.export_input source output count
    (by rw [memV, restV.sp]; exact flagU)
    (by rw [memV, value]; exact bound)
  refine WP.mono (exportBufferMasked_ok v input) ?_
  rintro t ⟨bytes, status, frameT, restT⟩
  rw [sharedV.product_read, memV, value] at bytes
  rw [memV] at frameT
  exact ⟨bytes, status, (frameU.mono (by simp)).trans (frameT.mono (by simp)),
    restU.trans ((restV.mono (by decide)).trans restT)⟩

end VG.Proof.Bignum.Arm
