module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtPrepareState
public import VerifiedGarbage.Impl.Bignum.Arm.PcFn
public import VerifiedGarbage.Impl.Bignum.Arm.CrtSetup
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Bignum.Arm.CrtSetupAll
import VerifiedGarbage.Proof.Bignum.Arm.PcHead
import VerifiedGarbage.Proof.Bignum.Arm.CrtSetupFrame
import VerifiedGarbage.Proof.Bignum.Arm.CrtLayout
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
import VerifiedGarbage.Proof.Framework.Block

/-! # Initialize all CRT workspaces while preserving the saved input arguments -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem crt_initialize_ok (s : State) {base np : BitVec 32} {size w k : Nat} {nb : List Byte}
    (h : CrtPrepareInput base np size w k nb s) :
    WP isa (.seq (.block PcFn.head) setupAll) s fun t => CrtInitialized base np size w k nb t ∧
      Frame [⟨State.addr base, size⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [WP.seq_iff]
  refine WP.mono (pcHead_ok s h.lengthValid.2 h.count) ?_
  rintro u ⟨count, zero, memU, restU⟩
  rw [h.width] at count
  refine WP.mono (crt_setupAll_ok u (h.context.congr restU.wr)
    ((restU.gpr .r0 (by decide)).trans h.ptr) count zero) ?_
  rintro t ⟨main, p, q, ptr, frame, restT⟩
  rw [memU] at frame
  have frame := crt_regions_frame h.workspace h.storageFits frame
  have rest : Rest roundClobbers s t := (restU.mono (by decide)).trans restT
  have source := h.source.after_frame frame rest
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.stackSeparate)
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.sourceSeparate)
  have stackSep : Region.Disjoint ⟨State.addr s.sp, 4⟩ ⟨State.addr base, size⟩ :=
    h.stackSeparate.sub_left (Region.sub_prefix (by decide))
  have saved := saved_base_kept frame stackSep h.saved rest.sp
  have ready : LayoutFrameReady base (workspaceWords w) w t :=
    ⟨⟨h.context.main.congr rest.wr, main.layout, main.width, ptr⟩,
      by rw [rest.rd, rest.wr, rest.sp]; exact h.stackRead,
      by rw [rest.sp]; exact h.source.stackSeparate.sub_left (Region.sub_prefix (by decide)), saved⟩
  have bytesFit := (crt_width_valid h.lengthValid).2.2
  rw [h.width] at bytesFit
  exact ⟨⟨h.workspace.congr rest.wr, h.context.congr rest.wr, ready, main, p, q, source,
    by rw [rest.wr, rest.sp]; exact h.stackWrite,
    by rw [rest.sp]; exact h.stackSeparate, h.storageFits,
    by have := h.lengthValid.1; omega, bytesFit⟩, frame, rest⟩

end VG.Proof.Bignum.Arm
