module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Top2
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Body
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block

/-! # An RSA key on ARMv7: a call's result (`key_ok`)

The push, the body (run with the regions `xRegs` and widened to the
caller's) and the restore.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Key
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Proof.Rsa.Arm.Keys VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Impl.RsaKeyGen.Arm.Key (code body)

/-- A call's result, as the body gives it. -/
def KPost (s t : State) : Prop :=
  (t.gpr .r0).toNat = Spec.RsaKeyGen.keyStatus (resv (mkP s) (sx s)) ∧
    ∀ i < 7, Spec.Rsa.bytesAt t.mem (State.addr (oPtr (mkP s) i)) (oLen (mkP s) i) = outE (mkP s) (sx s) i

section
variable {s : State}

/-- The body's regions are the frame and the caller's writable ones. -/
theorem CIn.xCovers (h : CIn s) : Covers (xRegs s) (pcPushed s).wr := by
  refine Covers.of_mem fun r hr => ?_
  simp only [xRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [pushed_wr, h.wr]
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.mem_cons_self
  · rw [h.rN]; simp
  · rw [h.rD]; simp
  · show cP s ∈ _; simp
  · rw [h.rQ]; simp
  · rw [h.rDp]; simp
  · rw [h.rDq]; simp
  · rw [h.rQi]; simp
  · show cS s ∈ _; simp

/-- The body's run, widened to the caller's regions. -/
theorem body_wide [VG.Proof.Rsa.Arm.Keys.InvLaw] (h : CIn s) :
    ∃ tr v, Exec isa body (sx s) tr v ∧ Exec isa body (pcPushed s) tr (v.withRegions s.rd (pcPushed s).wr) ∧
      Res (mkP s) (sx s) v := by
  have pre := in_k h
  obtain ⟨tr, v, run, res⟩ := body_vp.wp _ _ ⟨pre, pre, rfl, rfl, rfl, Frame.refl _ _⟩
  have cov := h.xCovers
  have run' := Exec.widen (rd := s.rd) (wr := (pcPushed s).wr) run
    (Covers.append (Covers.refl _) cov) cov
  simp only [State.withRegions_withRegions] at run'
  exact ⟨tr, v, run, run', res⟩

/-- A call's result. -/
theorem key_ok [VG.Proof.Rsa.Arm.Keys.InvLaw] (h : CIn s) : WP isa code s fun t => abiPreserved s t ∧ KPost s t := by
  have spLo := h.spLo; have spHi := h.spHi
  have spN : (s.sp - BitVec.ofNat 32 56).toNat = s.sp.toNat - 56 := FrameStack.sub_toNat' spLo
  unfold code
  refine WP.frame (by decide) spLo (by decide) ?_
  rw [WP.seq_iff]
  have pre := in_k h
  obtain ⟨tr, v, -, run', ⟨bo, r0, outs⟩⟩ := body_wide h
  refine WP.mono (Q := fun x => x = v.withRegions s.rd (pcPushed s).wr) ⟨tr, _, run', rfl⟩ ?_
  rintro _ rfl
  have vsp : v.sp = s.sp - BitVec.ofNat 32 56 := bo.sp
  have saved : Spill.Saved v.mem (State.addr (s.sp - 56)) s.gpr pcCalleeSaved :=
    (pc_push_callee_saved s spLo).frame (lo := 16) (hi := 56) (by decide) bo.frame (by
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact pre.sF.symm.sub_left (Offset.sub_base _ (by decide))
      · have : ∃ i, i < 7 ∧ r = oR (mkP s) i := by
          simp only [KP.outs, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
          exacts [⟨0, by decide, rfl⟩, ⟨1, by decide, rfl⟩, ⟨2, by decide, rfl⟩, ⟨3, by decide, rfl⟩,
            ⟨4, by decide, rfl⟩, ⟨5, by decide, rfl⟩, ⟨6, by decide, rfl⟩]
        obtain ⟨i, hi, rfl⟩ := this
        exact (pre.oF i hi).symm.sub_left (Offset.sub_base _ (by decide)))
  have fit : (v.withRegions s.rd (pcPushed s).wr).sp.toNat + 56 ≤ 2 ^ 32 := by
    show v.sp.toNat + 56 ≤ _; rw [vsp, spN]; omega
  have read : InRegions ((v.withRegions s.rd (pcPushed s).wr).rd ++ (v.withRegions s.rd (pcPushed s).wr).wr)
      (State.addr (v.withRegions s.rd (pcPushed s).wr).sp) 56 := by
    have m : (⟨State.addr (s.sp - BitVec.ofNat 32 56), 56⟩ : Region) ∈ (v.withRegions s.rd (pcPushed s).wr).wr := by
      rw [State.withRegions_wr]; exact List.mem_cons_self
    refine ⟨_, List.mem_append_right _ m, ?_⟩
    rw [State.withRegions_sp, vsp]; exact Region.contains_self _ _
  refine WP.mono (pc_restore_ok _ s.gpr fit read (by rw [State.withRegions_sp, vsp]; exact saved)) ?_
  rintro t ⟨restored, memT, restT⟩
  have ret : t.gpr .r0 = v.gpr .r0 := restT.gpr .r0 (by simp [pcCalleeSaved])
  refine ⟨⟨?_, ?_⟩, ?_, fun i hi => ?_⟩
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
  · rw [popped_sp, restT.sp, State.withRegions_sp, vsp]
    exact BitVec.sub_add_cancel _ _
  · rw [popped_gpr (by decide : Reg.r0 ≠ .r12), ret]; exact r0
  · rw [popped_mem, memT, State.withRegions_mem]; exact outs i hi

end

end VG.Proof.RsaKeyGen.Arm.Key
