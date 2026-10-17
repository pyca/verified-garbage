module

public import VerifiedGarbage.Proof.Bignum.Arm.PdBodyInput
public import VerifiedGarbage.Impl.Bignum.Arm.PublicFn
public import VerifiedGarbage.Proof.Bignum.Arm.PcPrepare
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Prepare the shared workspace for a validated public RSA modulus -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

theorem pdPrepareCore_ok (s : State) {base dst np ep xp : BitVec 32} {len k eLen N R : Nat} {eb xb : List Byte}
    (h : PdBodyInput base dst np ep xp len k eLen N R eb xb s)
    (count : s.gpr .r6 = BitVec.ofNat 32 k) :
    WP isa PublicFn.prepare s fun t => PdBodyInput base dst np ep xp len k eLen N R eb xb t ∧ PdImportInput base np len (Spec.Rsa.modulusWords k) t ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  obtain ⟨hw, hw', fits, _, _⟩ := pc_dimensions h.buffers.minLength h.buffers.maxLength h.buffers.space
  rw [PublicFn.prepare, WP.seq_iff]
  refine WP.mono (pcHead_ok s h.buffers.maxLength count) ?_
  rintro u ⟨limbs, zero, memU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (setup_frame_ok u (h.buffers.workspace.congr restU.wr) hw hw' fits
    ((restU.gpr .r0 (by simp)).trans h.ptr) limbs zero) ?_
  rintro v ⟨layoutV, widthV, ptrV, frameV, restV⟩
  rw [memU] at frameV
  have rv : Rest roundClobbers s v := (restU.mono (by simp [roundClobbers])).trans restV
  have stackV := h.stack.after_workspace frameV rv
  refine WP.mono (pcInputs_ok v stackV.pcStack) ?_
  rintro t ⟨source, _, memT, restT⟩
  have rest : Rest roundClobbers s t := rv.trans (restT.mono (by simp [roundClobbers]))
  have frame : Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem := by rw [memT]; exact frameV
  have stack := h.stack.after_workspace frame rest
  have buffers := h.buffers.after_workspace frame rest
  have body := h.after_workspace frame rest ((restT.gpr .r0 (by simp)).trans ptrV)
  have input : PdImportInput base np len (Spec.Rsa.modulusWords k) t :=
    ⟨⟨⟨buffers.workspace, by rw [memT]; exact layoutV, by rw [memT]; exact widthV,
      body.ptr⟩,
      by simpa only [VG.Proof.Mont.off, BitVec.add_zero] using stack.read (d := 0) (by decide) (by decide),
      stack.separate.sub_left (Region.sub_prefix (by decide)), stack.savedBase⟩,
      body.sourceFit, body.read, body.separate, source⟩
  exact ⟨body, input, frame, rest⟩

theorem pdPrepare_ok (s : State) {base dst pp ep xp : BitVec 32} {len k eLen N R : Nat} {eb xb : List Byte}
    (h : PdBodyInput base dst pp ep xp len k eLen N R eb xb s) :
    WP isa PdFn.prepare s fun t => PdBodyInput base dst pp ep xp len k eLen N R eb xb t ∧
      PdImportInput base pp len (Spec.Rsa.modulusWords k) t ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [PdFn.prepare, WP.seq_iff]
  refine WP.mono (pcInputs_ok s h.stack.pcStack) ?_
  rintro u ⟨_, count, mem, rest⟩
  have hu := h.of_mem mem rest ((rest.gpr .r0 (by simp)).trans h.ptr)
  refine WP.mono (pdPrepareCore_ok u hu count) ?_
  rintro t ⟨body, input, frame, keep⟩
  rw [mem] at frame
  exact ⟨body, input, frame, (rest.mono (by simp [roundClobbers])).trans keep⟩

end VG.Proof.Bignum.Arm
