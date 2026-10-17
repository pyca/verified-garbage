module

public import VerifiedGarbage.Proof.Rsa.Arm.PrivFnInput
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Callable checked private RSA restores the ARM procedure-call convention -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm VG.Proof.Mont

theorem privateFn_ok (v : CrtImpl) (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte}
    (h : PrivFnInput g bs s) :
    WP isa (privCode v) s fun t => abiPreserved s t ∧
      Spec.Rsa.writtenOutcome t.mem (State.addr g.output) g.length (t.gpr .r0)
        (Spec.Rsa.privateChecked (bs 0) (bs 1) (bs 2) (bs 3) (bs 4) (bs 5) (bs 6) (bs 7)) := by
  have stackFit : 56 ≤ s.sp.toNat := by have := h.stackFit; simp only [stackBytes] at this; omega
  have allocation : frameBytes ≤ (pcPushed s).sp.toNat := by
    change frameBytes ≤ (s.sp - BitVec.ofNat 32 56).toNat
    rw [FrameStack.sub_toNat' stackFit]
    have := h.stackFit
    simp only [stackBytes, frameBytes] at *
    omega
  unfold privCode code
  refine WP.frame (by decide) stackFit (by decide) ?_
  rw [WP.seq_iff]
  refine WP.alloc (by decide) allocation ?_
  refine WP.mono (privateBody_ok v (entered s) h.context h.output h.modulus h.count) ?_
  rintro u ⟨result, _, frame, rest⟩
  have spU : (freed frameBytes u).sp = (pcPushed s).sp := by
    change u.sp + BitVec.ofNat 32 frameBytes = _
    rw [rest.sp]
    exact BitVec.sub_add_cancel _ _
  have wrU : (freed frameBytes u).wr = (pcPushed s).wr := by
    change u.wr.tail = _
    rw [rest.wr]; rfl
  have fit : (freed frameBytes u).sp.toNat + 56 ≤ 2 ^ 32 := by
    rw [spU]
    change (s.sp - BitVec.ofNat 32 56).toNat + 56 ≤ 2 ^ 32
    rw [FrameStack.sub_toNat' stackFit]
    have := s.sp.isLt
    omega
  have saved : Spill.Saved (freed frameBytes u).mem (State.addr (freed frameBytes u).sp) s.gpr pcCalleeSaved := by
    rw [spU, freed_mem_eq]
    exact h.saved (t := u) frame
  have read : InRegions ((freed frameBytes u).rd ++ (freed frameBytes u).wr)
      (State.addr (freed frameBytes u).sp) 56 := by
    refine ⟨⟨State.addr (freed frameBytes u).sp, 56⟩, List.mem_append_right _ ?_, Region.contains_self _ _⟩
    rw [wrU, spU]
    exact List.mem_cons_self
  refine WP.mono (pc_restore_ok (freed frameBytes u) s.gpr fit read saved) ?_
  rintro t ⟨restored, memT, restT⟩
  have ret : t.gpr .r0 = u.gpr .r0 := restT.gpr .r0 (by simp [pcCalleeSaved])
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
  · rw [popped_sp, restT.sp, spU]
    exact BitVec.sub_add_cancel _ _
  · simp only [popped_gpr (by decide : Reg.r0 ≠ .r12), popped_mem, memT, ret, freed_mem_eq]
    exact result
end VG.Proof.Rsa.Arm
