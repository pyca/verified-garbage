module

public import VerifiedGarbage.Proof.Bignum.Arm.PcEntryReady
public import VerifiedGarbage.Proof.Bignum.Arm.PcBody
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Callable ARMv7 RSA precomputation preserves AAPCS and implements the shared result -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont

theorem pcFn_ok (s : State) {base dst src : BitVec 32} {len k : Nat}
    (h : PcFnInput base dst src len k s) :
    WP isa PcFn.code s fun t => abiPreserved s t ∧
      (match Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (State.addr src) k) with
      | some words => t.gpr .r0 = 1 ∧ Spec.Rsa.wordsAt t.mem (State.addr dst) (2 * Spec.Rsa.modulusWords k) = words
      | none => t.gpr .r0 = 0 ∧ Spec.Rsa.wordsAt t.mem (State.addr dst) (2 * Spec.Rsa.modulusWords k) =
          List.replicate (2 * Spec.Rsa.modulusWords k) 0) := by
  unfold PcFn.code
  refine WP.frame (by decide) h.stackFit (by decide) ?_
  rw [WP.seq_iff]
  refine WP.mono (pc_entry_ready s h) ?_
  rintro u ⟨ready, frameU, savedU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (pcBody_ok u ready.workspace ready.stack ready.minLength ready.maxLength ready.space
    ready.sourceFits ready.readable ready.sourceSeparate ready.outputFits ready.writable ready.outputSeparate
    ready.ptr ready.source ready.count) ?_
  rintro v ⟨result, frameV, restV⟩
  have bytes := rsa_bytes_frame frameU (by have := h.maxLength; omega : k < 2 ^ 64)
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.stackInput.symm)
  rw [bytes] at result
  have spV : v.sp = s.sp - BitVec.ofNat 32 56 := restV.sp.trans restU.sp
  have wrV : v.wr = (pcPushed s).wr := restV.wr.trans restU.wr
  have saved : Spill.Saved v.mem (State.addr v.sp) s.gpr pcCalleeSaved := by
    rw [restV.sp]
    apply savedU.frame (lo := 0) (hi := 56) (by decide) frameV
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [restU.sp]
    simp only [BitVec.add_zero, Nat.sub_zero]
    change (⟨State.addr (s.sp - BitVec.ofNat 32 56), 56⟩ : Region).Disjoint r
    rcases hr with rfl | rfl
    · simpa only [FrameStack.belowA, BitVec.add_zero, Nat.sub_zero] using h.stackWorkspace
    · simpa only [FrameStack.belowA, BitVec.add_zero, Nat.sub_zero] using h.stackOutput
  have fit : v.sp.toNat + 56 ≤ 2 ^ 32 := by
    rw [spV, FrameStack.sub_toNat' h.stackFit]
    have := s.sp.isLt
    omega
  have read : InRegions (v.rd ++ v.wr) (State.addr v.sp) 56 := by
    refine ⟨⟨State.addr v.sp, 56⟩, List.mem_append_right _ ?_, Region.contains_self _ _⟩
    rw [wrV, spV]
    exact List.mem_cons_self
  refine WP.mono (pc_restore_ok v s.gpr fit read saved) ?_
  rintro t ⟨restored, memT, restT⟩
  have ret : t.gpr .r0 = v.gpr .r0 := restT.gpr .r0 (by simp [pcCalleeSaved])
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro r hr
    have ne : r ≠ .r12 := by intro he; subst r; simp [preserved] at hr
    rw [popped_gpr ne]
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact restored (.r4, 16) (by simp [pcCalleeSaved])
    · exact restored (.r5, 20) (by simp [pcCalleeSaved])
    · exact restored (.r6, 24) (by simp [pcCalleeSaved])
    · exact restored (.r7, 28) (by simp [pcCalleeSaved])
    · exact restored (.r8, 32) (by simp [pcCalleeSaved])
    · exact restored (.r9, 36) (by simp [pcCalleeSaved])
    · exact restored (.r10, 40) (by simp [pcCalleeSaved])
    · exact restored (.r11, 44) (by simp [pcCalleeSaved])
    · exact restored (.lr, 52) (by simp [pcCalleeSaved])
  · rw [popped_sp, restT.sp, spV]
    exact BitVec.sub_add_cancel _ _
  · simp only [popped_gpr (by decide : Reg.r0 ≠ .r12), popped_mem, memT, ret]
    exact result

end VG.Proof.Bignum.Arm
