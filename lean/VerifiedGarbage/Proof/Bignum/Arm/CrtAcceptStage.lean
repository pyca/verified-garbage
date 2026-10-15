module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtAcceptInput
public import VerifiedGarbage.Proof.Bignum.Arm.CrtSavedSources
public import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedWorkspace
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Connect the ciphertext range check to the shared private RSA call state -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem crt_acceptStage_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtShared g bs s) (ready : LayoutFrameReady g.base (workspaceWords g.words) g.words s) :
    WP isa CrtFn.acceptInput s fun t => CrtShared g bs t ∧
      LayoutFrameReady g.base (workspaceWords g.words) g.words t ∧
      t.mem.readW (off (State.addr t.sp) 48) 32 =
        BitVec.ofNat 32 (decide (Spec.Rsa.os2ip (bs 1) < Spec.Rsa.os2ip (bs 0))).toNat ∧
      Frame (crtLiveMutable g s.sp) s.mem t.mem ∧ Rest roundClobbers s t := by
  have mainSub := crt_region_sub_workspace h.buffers.workspace h.buffers.storageFits
    (r := ⟨State.addr g.base, 8 * workspaceWords g.words⟩) (by simp [crtRegions])
  have input : CrtAcceptInput g.base g.input (workspaceWords g.words) g.words g.length (bs 1) s :=
    ⟨ready, h.main, h.inputSaved (by simp [crtRegions]),
      by have := h.buffers.lengthValid.1; omega, (crt_width_valid h.buffers.lengthValid).2.2,
      by have := h.stack.nowrap; omega, h.stack.write (by decide),
      (h.stack.separate.symm.sub_right (Offset.sub_base _ (by decide))).sub_left mainSub⟩
  refine WP.mono (crt_acceptInput_ok s input) ?_
  rintro t ⟨readyT, modulus, _, flag, frame, rest, mainT⟩
  rw [h.modulus] at flag
  exact ⟨h.after_main frame rest mainT modulus, readyT, flag,
    crt_workspace_frame h.buffers.workspace h.buffers.storageFits (by simp [crtRegions]) frame, rest⟩

end VG.Proof.Bignum.Arm
