module
public import VerifiedGarbage.Impl.Bignum.Arm.PdFn
public import VerifiedGarbage.Proof.Bignum.Arm.PdBodyInput
public import VerifiedGarbage.Proof.Bignum.Arm.PdInput
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Proof.Bignum.Arm.PcPush

import VerifiedGarbage.Proof.Bignum.Arm.PdEntryMemory
import VerifiedGarbage.Proof.Bignum.Arm.PdPush
import VerifiedGarbage.Proof.Bignum.Arm.PdEntry
import VerifiedGarbage.Proof.Bignum.Arm.PublicPush
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # Establish the public RSA body invariants from native arguments -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem pd_entry_ready (s : State) {base dst np ep xp : BitVec 32} {len k eLen N R : Nat}
    {eb xb : List Byte} (h : PdFnInput base dst np ep xp len k eLen N R eb xb s) :
    WP isa (.block PdFn.entry) (pcPushed s) fun t =>
      PdBodyInput base dst np ep xp len k eLen N R eb xb t ∧
      Frame [FrameStack.belowA s.sp 56] s.mem t.mem ∧
      Spill.Saved t.mem (State.addr t.sp) s.gpr pcCalleeSaved ∧ Rest roundClobbers (pcPushed s) t := by
  have pushFrame := FrameStack.pushed_frameA
    (rs := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]) h.stackFit
  have spNat : (pcPushed s).sp.toNat = s.sp.toNat - 56 := FrameStack.sub_toNat' h.stackFit
  obtain ⟨argRead, argEq⟩ := pd_push_arguments h
  have readBase := CallLay.inRegions_sub (off := 16) argRead (l := 4) (by decide) (by decide)
  have add16 : off (State.addr (pcPushed s).sp) 56 + BitVec.ofNat 64 16 = off (State.addr (pcPushed s).sp) 72 := by
    exact Offset.add_add _ 56 16
  rw [add16] at readBase
  have baseArg : (pcPushed s).mem.readW (off (State.addr (pcPushed s).sp) 72) 32 = base := by
    rw [public_push_argOffset h.stackFit 16, argEq.word (d := 16) (bits := 32) (by decide)]
    exact h.workspaceArg
  refine WP.mono (pdEntry_ok (pcPushed s) (by rw [spNat]; have := h.argFit; omega)
    (List.mem_cons_self) readBase baseArg) ?_
  rintro t ⟨ptr, mem, rest⟩
  obtain ⟨savedBase, savedOutput, savedSource, savedCount, outside, frameEntry⟩ := pdEntry_memory mem
  have frameEntryFull : Frame [FrameStack.belowA s.sp 56] (pcPushed s).mem t.mem :=
    frameEntry.sub (by intro r hr; simp only [List.mem_singleton] at hr; subst r
                       exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩)
  have frame := pushFrame.trans frameEntryFull
  have savedAll := pc_push_saved s h.stackFit
  have savedCallee := pdEntry_callee_saved (pc_push_callee_saved s h.stackFit) mem
  have keepBytes {p : BitVec 32} {n : Nat} {bs : List Byte} (bytes : PublicBytes p n bs s)
      (sep : (FrameStack.belowA s.sp 56).Disjoint ⟨State.addr p, n⟩) : PublicBytes p n bs t := by
    refine ⟨bytes.fits, ?_, ?_⟩
    · rw [rest.rd, rest.wr]
      exact InRegions_append_cons.mpr (Or.inr bytes.read)
    · exact (rsa_bytes_frame frame (by have := bytes.fits; omega)
        (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact sep.symm)).trans bytes.bytes
  refine ⟨⟨?_, ?_, ptr, h.sourceFit, ?_, h.modulusSeparate.symm, ?_, ?_, ?_⟩, frame, ?_, rest.mono (by simp [roundClobbers])⟩
  · refine ⟨⟨h.workspace.nowrap, ?_⟩, h.minLength, h.maxLength, h.space, h.exponentPositive, h.exponentFits,
      keepBytes h.exponent h.stackExponent, keepBytes h.input h.stackInput,
      h.outputFit, ?_, h.exponentSeparate, h.inputSeparate, h.outputSeparate, ?_, ?_, ?_⟩
    · rw [rest.wr]; exact List.mem_cons_of_mem _ h.workspace.writable
    · rw [rest.wr]
      obtain ⟨r, hr, hc⟩ := h.write
      exact ⟨r, List.mem_cons_of_mem _ hr, hc⟩
    · rw [rest.sp]; exact h.stackExponent.symm
    · rw [rest.sp]; exact h.stackInput.symm
    · rw [rest.sp]; exact h.stackOutput.symm
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [rest.sp, spNat]; have := h.argFit; omega
    · rw [rest.wr, rest.sp]; exact List.mem_cons_self
    · rw [rest.rd, rest.wr, rest.sp]; exact argRead
    · rw [rest.sp]; exact pd_push_separate h
    · rw [rest.sp]; exact savedBase
    · rw [rest.sp]; exact savedOutput.trans h.output
    · rw [rest.sp, savedSource]
      exact (savedAll (.r2, 8) (by simp [pcAllSaved])).trans h.source
    · rw [rest.sp]; exact savedCount.trans h.count
    · rw [rest.sp, outside_read32 outside (d := 56) (by decide) (by decide)]
      change (pcPushed s).mem.readW (off (State.addr (pcPushed s).sp) 56) 32 = ep
      rw [public_push_argAddr h.stackFit]
      have keep := argEq.word (d := 0) (bits := 32) (by decide)
      simp only [BitVec.add_zero] at keep
      exact keep.trans h.exponentArg
    · rw [rest.sp, outside_read32 outside (d := 60) (by decide) (by decide)]
      change (pcPushed s).mem.readW (off (State.addr (pcPushed s).sp) 60) 32 = BitVec.ofNat 32 eLen
      rw [public_push_argOffset h.stackFit 4, argEq.word (d := 4) (bits := 32) (by decide)]
      exact h.exponentCountArg
    · rw [rest.sp, outside_read32 outside (d := 64) (by decide) (by decide)]
      change (pcPushed s).mem.readW (off (State.addr (pcPushed s).sp) 64) 32 = xp
      rw [public_push_argOffset h.stackFit 8, argEq.word (d := 8) (bits := 32) (by decide)]
      exact h.inputArg
  · rw [rest.rd, rest.wr]
    exact InRegions_append_cons.mpr (Or.inr h.preRead)
  · rw [rest.sp]; exact h.stackModulus.symm
  · have eq : WorkspaceEq (State.addr np) (16 * Spec.Rsa.modulusWords k) s.mem t.mem := WorkspaceEq.of_frame (by have := h.sourceFit; omega) frame
      (fun r hr => by simp only [List.mem_singleton] at hr; subst r; exact h.stackModulus.symm)
    have read := eq.read (d := 0) (8 * Spec.Rsa.modulusWords k) (by omega)
    simp only [BitVec.add_zero] at read
    rw [read]; exact h.modulus
  · have eq : WorkspaceEq (State.addr np) (16 * Spec.Rsa.modulusWords k) s.mem t.mem := WorkspaceEq.of_frame (by have := h.sourceFit; omega) frame
      (fun r hr => by simp only [List.mem_singleton] at hr; subst r; exact h.stackModulus.symm)
    rw [eq.read (d := 8 * Spec.Rsa.modulusWords k) (8 * Spec.Rsa.modulusWords k) (by omega)]
    exact h.r2
  · rw [rest.sp]; exact savedCallee

end VG.Proof.Bignum.Arm
