module

public import VerifiedGarbage.Proof.Bignum.Arm.PublicArithmetic
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

structure PublicBodyInput (base dst np ep xp : BitVec 32) (len k eLen : Nat)
    (nb eb xb : List Byte) (s : State) : Prop where
  buffers : PublicBuffers base dst np ep xp len k eLen nb eb xb s
  stack : PublicStack base dst np ep xp len k eLen s
  ptr : s.gpr .r0 = base

theorem PublicBodyInput.of_mem {s t : State} {base dst np ep xp : BitVec 32} {len k eLen : Nat}
    {nb eb xb : List Byte} {rs : List Reg}
    (h : PublicBodyInput base dst np ep xp len k eLen nb eb xb s)
    (mem : t.mem = s.mem) (rest : Rest rs s t) (ptr : t.gpr .r0 = base) :
    PublicBodyInput base dst np ep xp len k eLen nb eb xb t := by
  have frame : Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem := by rw [mem]; exact Frame.refl _ _
  exact ⟨h.buffers.after_workspace frame rest, h.stack.after_workspace frame rest, ptr⟩

structure PublicValidInput (base dst np ep xp : BitVec 32) (len k eLen : Nat)
    (nb eb xb : List Byte) (s : State) : Prop extends PublicBodyInput base dst np ep xp len k eLen nb eb xb s where
  valid : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true
  source : s.gpr .r4 = np
  count : s.gpr .r6 = BitVec.ofNat 32 k

structure PublicPrepared (base dst np ep xp : BitVec 32) (len k eLen : Nat)
    (nb eb xb : List Byte) (s : State) : Prop where
  buffers : PublicBuffers base dst np ep xp len k eLen nb eb xb s
  stack : PublicStack base dst np ep xp len k eLen s
  input : PrecomputeInput base np len (Spec.Rsa.modulusWords k) k s

theorem publicPrepare_ok (s : State) {base dst np ep xp : BitVec 32} {len k eLen : Nat} {nb eb xb : List Byte}
    (h : PublicValidInput base dst np ep xp len k eLen nb eb xb s) :
    WP isa PublicFn.prepare s fun t => PublicPrepared base dst np ep xp len k eLen nb eb xb t ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  obtain ⟨hw, hw', fits, bytesFit, _⟩ := pc_dimensions h.buffers.minLength h.buffers.maxLength h.buffers.space
  obtain ⟨odd, large, _⟩ := VG.Proof.Bignum.valid_facts h.valid h.buffers.minLength
  rw [PublicFn.prepare, WP.seq_iff]
  refine WP.mono (pcHead_ok s h.buffers.maxLength h.count) ?_
  rintro u ⟨limbs, zero, memU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (setup_frame_ok u (h.buffers.workspace.congr restU.wr) hw hw' fits
    ((restU.gpr .r0 (by simp)).trans h.ptr) limbs zero) ?_
  rintro v ⟨layoutV, widthV, ptrV, frameV, restV⟩
  rw [memU] at frameV
  have rv : Rest roundClobbers s v := (restU.mono (by simp [roundClobbers])).trans restV
  have stackV := h.stack.after_workspace frameV rv
  refine WP.mono (pcInputs_ok v stackV.pcStack) ?_
  rintro t ⟨source, count, memT, restT⟩
  have rest : Rest roundClobbers s t := rv.trans (restT.mono (by simp [roundClobbers]))
  have frame : Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem := by rw [memT]; exact frameV
  have stack := h.stack.after_workspace frame rest
  have buffers := h.buffers.after_workspace frame rest
  have input : PrecomputeInput base np len (Spec.Rsa.modulusWords k) k t :=
    ⟨⟨buffers.workspace, by rw [memT]; exact layoutV, by rw [memT]; exact widthV,
      (restT.gpr .r0 (by simp)).trans ptrV,
      by simpa only [VG.Proof.Mont.off, BitVec.add_zero] using stack.read (d := 0) (by decide) (by decide),
      stack.separate.sub_left (Region.sub_prefix (by decide)), stack.savedBase⟩,
      by have := buffers.minLength; omega, bytesFit, buffers.modulus.fits, buffers.modulus.read,
      buffers.modulusSeparate, source, count, by rw [buffers.modulus.bytes]; exact large,
      by rw [buffers.modulus.bytes]; exact odd⟩
  exact ⟨⟨buffers, stack, input⟩, frame, rest⟩

theorem publicPrecompute_ok (s : State) {base dst np ep xp : BitVec 32} {len k eLen : Nat} {nb eb xb : List Byte}
    (h : PublicPrepared base dst np ep xp len k eLen nb eb xb s) :
    WP isa precompute s fun t => PublicArithmetic base dst np ep xp len k eLen nb eb xb t ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have countFit := (pc_dimensions h.buffers.minLength h.buffers.maxLength h.buffers.space).2.2.2.2
  refine WP.mono (precompute_ok s h.input.workspace h.input.layout h.input.width h.input.positive h.input.fits
    h.input.sourceFits h.input.readable h.input.separate h.input.ptr h.input.source h.input.count
    h.input.stackRead h.input.stackSep h.input.saved h.input.large h.input.odd countFit) ?_
  rintro t ⟨done, modulus, r2, frame, rest⟩
  rw [h.buffers.modulus.bytes] at modulus r2
  have ready : ArithmeticReady base len (Spec.Rsa.modulusWords k) t :=
    ⟨done.workspace, done.layout, done.width, done.ptr, done.inverse,
      by rw [modulus, ← h.buffers.modulus.bytes]; exact h.input.large, done.stackRead, done.stackSep, done.saved⟩
  exact ⟨⟨(h.buffers.after_workspace frame rest).data, h.stack.after_workspace frame rest, ready, modulus, h.buffers.modulus.length,
    by rw [← h.buffers.modulus.bytes]; exact h.input.odd, r2⟩, frame, rest⟩

end VG.Proof.Bignum.Arm
