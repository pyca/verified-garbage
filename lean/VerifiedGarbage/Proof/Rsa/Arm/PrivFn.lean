module

public import VerifiedGarbage.Proof.Rsa.Arm.PrivFnInput
public import VerifiedGarbage.Proof.Rsa.Arm.PrivBody
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Arm.Call
import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Rsa.Arm.PrivRegions
import VerifiedGarbage.Proof.Rsa.PrivCheck

/-! # Callable checked private RSA restores the ARM procedure-call convention -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm VG.Proof.Mont

theorem codeWith_ok (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte} {Q : State → Prop}
    {b : Prog isa}
    (hb : ∀ s, PrivContext g bs s → s.gpr .r0 = g.output → s.gpr .r2 = g.sources 0 →
      s.gpr .r3 = BitVec.ofNat 32 g.length → Q s → WP isa b s (BodyPost g bs s))
    (h : PrivFnInput g bs s) (q : Q (entered s)) :
    WP isa (codeWith b) s fun t => abiPreserved s t ∧
      Spec.Rsa.writtenOutcome t.mem (State.addr g.output) g.length (t.gpr .r0)
        (Spec.Rsa.privateChecked (bs 0) (bs 1) (bs 2) (bs 3) (bs 4) (bs 5) (bs 6) (bs 7)) := by
  have stackFit : 56 ≤ s.sp.toNat := by have := h.stackFit; simp only [stackBytes] at this; omega_using [this]
  have allocation : frameBytes ≤ (pcPushed s).sp.toNat := by
    change frameBytes ≤ (s.sp - BitVec.ofNat 32 56).toNat
    rw [FrameStack.sub_toNat' stackFit]
    have := h.stackFit
    simp only [stackBytes, frameBytes] at *
    omega_using [this]
  unfold codeWith
  refine WP.frame (by decide) stackFit (by decide) ?_
  rw [WP.seq_iff]
  refine WP.alloc (by decide) allocation ?_
  refine WP.mono (hb (entered s) h.context h.output h.modulus h.count q) ?_
  rintro u ⟨result, _, frame, rest⟩ ml ul hfl
  change Frame [⟨State.addr (entered s).sp, frameBytes⟩] u.mem ml at hfl
  rw [h.context.sp] at hfl
  have spU : ({ freed frameBytes u with mem := ml, unknowns := ul } : State).sp = (pcPushed s).sp := by
    change u.sp + BitVec.ofNat 32 frameBytes = _
    rw [rest.sp]
    exact BitVec.sub_add_cancel _ _
  have wrU : ({ freed frameBytes u with mem := ml, unknowns := ul } : State).wr = (pcPushed s).wr := by
    change u.wr.tail = _
    rw [rest.wr]; rfl
  have fit : ({ freed frameBytes u with mem := ml, unknowns := ul } : State).sp.toNat + 56 ≤ 2 ^ 32 := by
    rw [spU]
    change (s.sp - BitVec.ofNat 32 56).toNat + 56 ≤ 2 ^ 32
    rw [FrameStack.sub_toNat' stackFit]
    have := s.sp.isLt
    omega_using []
  have saved : Spill.Saved ({ freed frameBytes u with mem := ml, unknowns := ul } : State).mem (State.addr ({ freed frameBytes u with mem := ml, unknowns := ul } : State).sp) s.gpr pcCalleeSaved := by
    rw [spU]
    refine (h.saved (t := u) frame).frame (lo := 0) (hi := 56) (by decide) hfl fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst r
    change (⟨State.addr (pcPushed s).sp + BitVec.ofNat 64 0, 56 - 0⟩ : Region).Disjoint _
    simp only [BitVec.add_zero, Nat.sub_zero, h.savedAddr]
    exact h.context.valid.innerSaved.symm
  have read : InRegions (({ freed frameBytes u with mem := ml, unknowns := ul } : State).rd ++ ({ freed frameBytes u with mem := ml, unknowns := ul } : State).wr)
      (State.addr ({ freed frameBytes u with mem := ml, unknowns := ul } : State).sp) 56 := by
    refine ⟨⟨State.addr ({ freed frameBytes u with mem := ml, unknowns := ul } : State).sp, 56⟩, List.mem_append_right _ ?_, Region.contains_self _ _⟩
    rw [wrU, spU]
    exact List.mem_cons_self
  refine WP.mono (pc_restore_ok ({ freed frameBytes u with mem := ml, unknowns := ul } : State) s.gpr fit read saved) ?_
  rintro t ⟨restored, memT, restT⟩ m₂ u₂ hfl₂
  change Frame [⟨State.addr (pcPushed s).sp, 56⟩] t.mem m₂ at hfl₂
  rw [h.savedAddr] at hfl₂
  have lenFit : g.length < 2 ^ 64 := by have := h.context.valid.maxLength; omega_using [this]
  have outEq : Spec.Rsa.bytesAt m₂ (State.addr g.output) g.length = Spec.Rsa.bytesAt u.mem (State.addr g.output) g.length := by
    rw [VG.Proof.Rsa.rsa_bytes_frame hfl₂ lenFit (fun r hr => by
        simp only [List.mem_singleton] at hr; subst r
        exact (h.context.valid.stackOutput.sub_left h.context.valid.savedSub).symm), memT]
    exact VG.Proof.Rsa.rsa_bytes_frame hfl lenFit (fun r hr => by
        simp only [List.mem_singleton] at hr; subst r
        exact (h.context.valid.stackOutput.sub_left h.context.valid.innerSub).symm)
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
  · dsimp only
    rw [popped_gpr (by decide : Reg.r0 ≠ .r12), ret]
    revert result
    cases Spec.Rsa.privateChecked (bs 0) (bs 1) (bs 2) (bs 3) (bs 4) (bs 5) (bs 6) (bs 7) <;>
      simp only [Spec.Rsa.writtenOutcome, outEq] <;> exact id

theorem privateFn_ok (v : CrtImpl) (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte}
    (h : PrivFnInput g bs s) :
    WP isa (privCode v) s fun t => abiPreserved s t ∧
      Spec.Rsa.writtenOutcome t.mem (State.addr g.output) g.length (t.gpr .r0)
        (Spec.Rsa.privateChecked (bs 0) (bs 1) (bs 2) (bs 3) (bs 4) (bs 5) (bs 6) (bs 7)) :=
  codeWith_ok (Q := fun _ => True) s (fun s h o m c _ => privateBody_ok v s h o m c) h trivial
end VG.Proof.Rsa.Arm
