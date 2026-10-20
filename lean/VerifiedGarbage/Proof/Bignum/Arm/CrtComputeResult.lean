module
public import VerifiedGarbage.Proof.Bignum.Arm.CrtResultBound

import VerifiedGarbage.Proof.Bignum.Arm.CrtComputeStage
import VerifiedGarbage.Proof.Framework.Block

/-! # The computed output satisfies the shared private-CRT result specification -/

@[expose] public section

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
    (h : CrtShared g bs s) (ready : LayoutFrameReady g.base (VG.Impl.Bignum.Arm.Crt.workspaceWords g.words) g.words s) :
    WP isa (.seq CrtFn.validate CrtFn.compute) s fun t =>
      Spec.Rsa.written t.mem (State.addr g.output) g.length (t.gpr .r0)
        (Spec.Rsa.privateCrt (bs 0) (bs 1) (bs 2) (bs 3) (bs 4) (bs 5) (bs 6)) ∧
      Frame (crtLiveMutable g s.sp ++ [⟨State.addr g.output, g.length⟩]) s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [WP.seq_iff]
  refine WP.mono (crt_validateStage_ok s h ready) ?_
  rintro u ⟨sharedU, readyU, p, q, flag, frameU, restU⟩
  refine WP.mono (crt_computeStage_ok u sharedU readyU p q flag) ?_
  rintro t ⟨bytes, status, frameT, restT⟩
  rw [restU.sp] at frameT
  exact ⟨crt_computed_written h bytes status,
    (frameU.mono (fun _ hr => List.mem_append_left _ hr)).trans frameT, restU.trans restT⟩

end VG.Proof.Bignum.Arm
