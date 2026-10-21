module

public import VerifiedGarbage.Proof.Bignum.Arm.PcInput
public import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeState
import VerifiedGarbage.Proof.Bignum.Arm.SetupFrame
import VerifiedGarbage.Proof.Bignum.Arm.PcHead
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Block

/-! # Workspace preparation establishes the modular-arithmetic invariants -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

structure PcValidInput (base dst src : BitVec 32) (len k : Nat) (s : State) : Prop extends
    PcBodyInput base dst src len k s where
  valid : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k)) k = true

structure PcPrepared (base dst src : BitVec 32) (len k : Nat) (s : State) : Prop where
  input : PrecomputeInput base src len (Spec.Rsa.modulusWords k) k s
  buffers : PcBuffers base dst src len k s
  stack : PcStack base dst src len k s

theorem PcBuffers.congr {base dst src : BitVec 32} {len k : Nat} {s t : State} {rs : List Reg}
    (h : PcBuffers base dst src len k s) (rest : Rest rs s t) : PcBuffers base dst src len k t :=
  ⟨h.workspace.congr rest.wr, h.minLength, h.maxLength, h.space, h.sourceFits,
    by rw [rest.rd, rest.wr]; exact h.readable,
    h.sourceSeparate, h.outputFits, by rw [rest.wr]; exact h.writable, h.outputSeparate⟩

theorem pcPrepare_frame_ready (s : State) {base dst src : BitVec 32} {len k : Nat}
    (h : PcValidInput base dst src len k s) :
    WP isa (.seq (.block PcFn.head) (.seq setup (.block PcFn.inputs))) s (fun t => PcPrepared base dst src len k t ∧ Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem) := by
  obtain ⟨hw, hw', fits, bytesFit, _⟩ := pc_dimensions h.minLength h.maxLength h.space
  obtain ⟨odd, large, _⟩ := VG.Proof.Bignum.valid_facts h.valid h.minLength
  rw [WP.seq_iff]
  refine WP.mono (pcHead_ok s h.maxLength h.count) ?_
  rintro u ⟨limbs, zero, memU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (setup_frame_ok u (h.workspace.congr restU.wr) hw hw' fits
    ((restU.gpr .r0 (by simp)).trans h.ptr) limbs zero) ?_
  rintro v ⟨layoutV, widthV, ptrV, frameV, restV⟩
  rw [memU] at frameV
  have rv : Rest roundClobbers s v := (restU.mono (by simp [roundClobbers])).trans restV
  refine WP.mono (pcInputs_ok v (h.stack.after_workspace frameV rv)) ?_
  rintro z ⟨sourceZ, countZ, memZ, restZ⟩
  have rz : Rest roundClobbers s z := rv.trans (restZ.mono (by simp [roundClobbers]))
  have frameZ : Frame [⟨State.addr base, 8 * len⟩] s.mem z.mem := by rw [memZ]; exact frameV
  have stackZ := h.stack.after_workspace frameZ rz
  have inputZ := rsa_bytes_frame frameZ (by have := h.maxLength; omega : k < 2 ^ 64)
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.sourceSeparate)
  refine ⟨?_, frameZ⟩
  refine ⟨⟨⟨h.workspace.congr rz.wr, ?_, ?_, ?_, ?_, ?_, stackZ.savedBase⟩,
    by have := h.minLength; omega, bytesFit, h.sourceFits, ?_, h.sourceSeparate, sourceZ, countZ, ?_, ?_⟩,
    h.toPcBuffers.congr rz, stackZ⟩
  · rw [memZ]; exact layoutV
  · rw [memZ]; exact widthV
  · exact (restZ.gpr .r0 (by simp)).trans ptrV
  · simpa only [VG.Proof.Mont.off, BitVec.add_zero] using stackZ.read (d := 0) (by decide)
  · exact stackZ.separate.sub_left (Region.sub_prefix (by decide))
  · rw [rz.rd, rz.wr]; exact h.readable
  · rw [inputZ]; exact large
  · rw [inputZ]; exact odd

theorem pcPrepare_ready (s : State) {base dst src : BitVec 32} {len k : Nat}
    (h : PcValidInput base dst src len k s) :
    WP isa (.seq (.block PcFn.head) (.seq setup (.block PcFn.inputs))) s (PcPrepared base dst src len k) :=
  WP.mono (pcPrepare_frame_ready s h) (fun _ j => j.1)

theorem pcPrepare_public_ready (s : State) {base dst src : BitVec 32} {len k : Nat} {nb : List Byte}
    (h : PcValidInput base dst src len k s) (bytes : Spec.Rsa.bytesAt s.mem (State.addr src) k = nb) :
    WP isa (.seq (.block PcFn.head) (.seq setup (.block PcFn.inputs))) s fun t =>
      PcPrepared base dst src len k t ∧ Spec.Rsa.bytesAt t.mem (State.addr src) k = nb := by
  refine WP.mono (pcPrepare_frame_ready s h) ?_
  rintro t ⟨prepared, frame⟩
  exact ⟨prepared, (rsa_bytes_frame frame (by have := h.maxLength; omega : k < 2 ^ 64)
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.sourceSeparate)).trans bytes⟩

end VG.Proof.Bignum.Arm
