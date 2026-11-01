module
public import VerifiedGarbage.Proof.Rsa.Arm.RvTop2

import VerifiedGarbage.Proof.Rsa.Arm.RvTop3
public import VerifiedGarbage.Proof.Rsa.Arm.RvBody
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block

/-! # `vg_rsa_recover_primes` on ARMv7: a call's result (`rv_ok`)

The push, the entry, the body (run with the regions `xRegs` and widened to
the caller's) and the restore.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.Bignum.Arm

section
variable {s : State}

/-- The body's regions are within the frame and the caller's writable ones. -/
theorem CIn.xCovers (h : CIn s) (sz : Sizes (mkP s)) : Covers (xRegs s) (pcPushed s).wr := by
  have hf : (mkP s).B.toNat + (mkP s).Z ≤ 2 ^ 32 := h.fS
  have pl := h.pl; have ql := h.ql
  have mS : cS s ∈ (pcPushed s).wr := by rw [pushed_wr, h.wr]; simp
  refine Covers.of_sub fun r hr => ?_
  simp only [xRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self, 0, by rw [BitVec.add_zero]; rfl, Nat.le_of_eq rfl⟩
  · exact ⟨cP s, by rw [pushed_wr, h.wr]; simp, 0, by rw [BitVec.add_zero]; rfl,
      by show 0 + (stackArg s 1).toNat ≤ (s.gpr .r1).toNat; omega⟩
  · exact ⟨cQ s, by rw [pushed_wr, h.wr]; simp, 0, by rw [BitVec.add_zero]; rfl,
      by show 0 + (stackArg s 1).toNat ≤ (s.gpr .r3).toNat; omega⟩
  · exact ⟨cS s, mS, 0, by rw [BitVec.add_zero]; rfl, Nat.le_of_eq (Nat.zero_add _)⟩
  · refine ⟨cS s, mS, (mkP s).oM, by show State.addr (mkP s).M0 = State.addr (stackArg s 6) + _; rw [M0_addr sz hf]; rfl, ?_⟩
    show (mkP s).oM + 8 * (mkP s).lenM ≤ (mkP s).Z
    rw [sz.endM]; exact Nat.le_trans (arr_mono (show mBase + 8 ≤ nArr by decide)) sz.fits

/-- The callee-saved registers' slots after the entry. -/
theorem CIn.savedE (h : CIn s) : Spill.Saved (entryMem s) (State.addr (s.sp - 56)) s.gpr pcCalleeSaved :=
  (pc_push_callee_saved s h.spLo).frame (lo := 16) (hi := 56) (by decide)
    ((Frame.refl [⟨off (State.addr (s.sp - 56)) 4, 4⟩] _).writeW (List.mem_singleton_self _) _
      (Region.contains_self _ _)) (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (Or.inr (by decide)) (by decide) (by decide))

/-- A call's result. -/
theorem rv_okWith (body : Prog isa) (bodyProof : BodyVerified body) (h : CIn s) :
    WP isa (codeWith body) s fun t => abiPreserved s t ∧
      Spec.Rsa.writtenAll t.mem [(State.addr (s.gpr .r0), (stackArg s 1).toNat),
        (State.addr (s.gpr .r2), (stackArg s 1).toNat)] (t.gpr .r0)
        ((Spec.Rsa.primesKey (Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat)
          (Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 2)) (stackArg s 3).toNat)
          (Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 4)) (stackArg s 5).toNat)).1.map
          fun v => [v.1, v.2]) := by
  have spLo := h.spLo; have spHi := h.spHi
  have spN : (s.sp - BitVec.ofNat 32 56).toNat = s.sp.toNat - 56 := FrameStack.sub_toNat' spLo
  unfold codeWith
  refine WP.frame (by decide) spLo (by decide) ?_
  rw [WP.seq_iff]
  refine WP.mono (entry_run h) fun u ⟨usp, urd, uwr, umem, uz⟩ => ?_
  rw [WP.seq_iff]
  have pre := in_x h usp urd umem
  have sz := pre.sizes
  obtain ⟨tr, v, run, bo, res⟩ := bodyProof.wp _ _ ⟨⟨pre, rfl, rfl, rfl, Frame.refl _ _⟩, uz⟩
  have cov := h.xCovers sz
  have run' := Exec.widen (rd := u.rd) (wr := u.wr) run
    (Covers.append (Covers.refl _) (by rw [uwr]; exact cov)) (by rw [uwr]; exact cov)
  simp only [State.withRegions_withRegions, State.withRegions_self] at run'
  refine WP.mono (Q := fun x => x = v.withRegions u.rd u.wr) ⟨tr, _, run', rfl⟩ ?_
  rintro _ rfl
  have vsp : v.sp = s.sp - BitVec.ofNat 32 56 := bo.sp.trans usp
  have saved : Spill.Saved v.mem (State.addr (s.sp - 56)) s.gpr pcCalleeSaved :=
    h.savedE.frame (lo := 16) (hi := 56) (by decide) (by rw [← umem]; exact bo.frame) (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact pre.sF.symm.sub_left (Offset.sub_base _ (by decide))
      · exact Offset.disjoint_base _ (by decide) (by decide)
      · exact pre.pF.symm.sub_left (Offset.sub_base _ (by decide))
      · exact pre.qF.symm.sub_left (Offset.sub_base _ (by decide)))
  have fit : (v.withRegions u.rd u.wr).sp.toNat + 56 ≤ 2 ^ 32 := by
    show v.sp.toNat + 56 ≤ _; rw [vsp, spN]; omega
  have read : InRegions ((v.withRegions u.rd u.wr).rd ++ (v.withRegions u.rd u.wr).wr)
      (State.addr (v.withRegions u.rd u.wr).sp) 56 := by
    have m : (⟨State.addr (s.sp - BitVec.ofNat 32 56), 56⟩ : Region) ∈ (v.withRegions u.rd u.wr).wr := by
      rw [State.withRegions_wr, uwr]; exact List.mem_cons_self
    refine ⟨_, List.mem_append_right _ m, ?_⟩
    rw [State.withRegions_sp, vsp]; exact Region.contains_self _ _
  refine WP.mono (pc_restore_ok _ s.gpr fit read (by rw [State.withRegions_sp, vsp]; exact saved)) ?_
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
  · rw [popped_sp, restT.sp, State.withRegions_sp, vsp]
    exact BitVec.sub_add_cancel _ _
  · have dEq : dB (mkP s) (u.withRegions u.rd (xRegs s)) =
        Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 4)) (stackArg s 5).toNat := by
      show Spec.Rsa.bytesAt u.mem _ _ = _
      rw [umem]; exact h.bytes (R := cD s) h.Fd (Nat.le_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide)))
    simp only [popped_gpr (by decide : Reg.r0 ≠ .r12), popped_mem, memT, ret, State.withRegions_mem]
    rw [dEq] at res
    exact res

end

theorem rv_ok [VG.Proof.Rsa.Arm.Keys.InvLaw] {s : State} (h : CIn s) :
    WP isa code s fun t => abiPreserved s t ∧
      Spec.Rsa.writtenAll t.mem [(State.addr (s.gpr .r0), (stackArg s 1).toNat),
        (State.addr (s.gpr .r2), (stackArg s 1).toNat)] (t.gpr .r0)
        ((Spec.Rsa.primesKey (Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat)
          (Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 2)) (stackArg s 3).toNat)
          (Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 4)) (stackArg s 5).toNat)).1.map
          fun v => [v.1, v.2]) :=
  rv_okWith (.ite .eq valid fail) body_vp h

end VG.Proof.Rsa.Arm.Recover
