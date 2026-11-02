module
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Fin4
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Top2

import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Top3
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Fin5
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.MillerRabin.Arm.Run
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Trial

/-! # A candidate on ARMv7: a call's result (`cand_ok`)

The push, the body (the entry, then the body proper, run with the regions
`xRegs` and widened to the caller's) and the restore.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Cand
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.MillerRabin.Arm (RoundImpl)

/-- The candidate's result, from the caller's memory. -/
def resC (s : State) : Option (Spec.RsaKeyGen.Candidate × Spec.RsaKeyGen.Rand) :=
  Spec.RsaKeyGen.candidateOp (s.gpr .r1).toNat
    (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat)
    (Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 1)) (stackArg s 2).toNat)
    (Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 3)) (stackArg s 4).toNat)

/-- A call's result. -/
def CPost (s t : State) : Prop :=
  (t.gpr .r0).toNat = Spec.RsaKeyGen.candidateStatus (resC s) ∧
    Spec.Rsa.bytesAt t.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat =
      (match resC s with
        | some (.prime c, _) => Spec.Rsa.i2osp c (s.gpr .r1).toNat
        | _ => List.replicate (s.gpr .r1).toNat 0) ∧
    Spec.Rsa.wordsAt t.mem (State.addr (s.gpr .r2)) 1 =
      [BitVec.ofNat 64 (match resC s with
        | some (_, rest) => (stackArg s 4).toNat - rest.length
        | none => 0)]

section
variable {s t : State}

theorem res_c (h : CIn s) (mt : t.mem = (pcPushed s).mem.writeW (off (State.addr (mkP s).sp) 48) (s.gpr .r0)) :
    res (mkP s) t = resC s := by
  have bP := h.bytesT mt (R := cP s) h.Fp (by have := h.fp; show (stackArg s 2).toNat ≤ _; omega)
  have bR := h.bytesT mt (R := cR s) h.Fr (by have := h.fr; show (stackArg s 4).toNat ≤ _; omega)
  show Spec.RsaKeyGen.candidateOp _ _ (Spec.Rsa.bytesAt t.mem (cP s).base (cP s).len)
    (Spec.Rsa.bytesAt t.mem (cR s).base (cR s).len) = _
  rw [bP, bR]; rfl

/-- The body's regions are the frame and the caller's writable ones. -/
theorem CIn.xCovers (h : CIn s) {σ : State} (pre : In (mkP s) σ) : Covers (xRegs s) (pcPushed s).wr := by
  refine Covers.of_forall fun r hr => ?_
  simp only [xRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [pushed_wr, h.wr]
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact Covers.of_mem fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self
  · exact Covers.of_mem fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_of_mem _ (List.mem_cons_self (a := cO s))
  · exact Covers.of_mem fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self (a := cU s)))
  · exact Covers.of_mem fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self (a := cS s))))
  · refine Covers.of_sub fun r hr => ⟨cS s,
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self (a := cS s)))),
      (mkP s).oM, ?_, ?_⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact pre.M0_addr
    · simp only [List.mem_singleton] at hr; subst hr
      show (mkP s).oM + 8 * (mkP s).lenM ≤ (mkP s).Z
      rw [pre.endM]; exact Nat.le_trans (arr_mono (show mBase + 8 ≤ nArr by decide)) pre.fits

/-- The body's run, widened to the caller's regions. -/
theorem body_wide [VG.Proof.Rsa.Arm.Keys.InvLaw] (v : RoundImpl) (h : CIn s) :
    ∃ tr w t, Exec isa (body v.name v.code) (pcPushed s) tr (w.withRegions s.rd (pcPushed s).wr) ∧
      Exec isa (body v.name v.code) (sx s) tr w ∧
      In (mkP s) t ∧ t.sp = (mkP s).sp ∧
      t.mem = (pcPushed s).mem.writeW (off (State.addr (mkP s).sp) 48) (s.gpr .r0) ∧
      RF (mkP s) (In (mkP s)) (stR (mkP s)) (outR (mkP s)) (usedR (mkP s)) t w := by
  obtain ⟨tr1, t, e1, pre, st, rt, wt, mt⟩ := entry_ok h
  obtain ⟨tr2, w, e2, rf⟩ := (candBody_vp v).wp t t ⟨pre, ⟨pre, rfl, rfl, rfl, Frame.refl _ _⟩⟩
  have run : Exec isa (body v.name v.code) (sx s) (tr1 ++ tr2) w := Exec.seq e1 e2
  have cov := h.xCovers pre
  have run' := Exec.widen (rd := s.rd) (wr := (pcPushed s).wr) run (Covers.append (Covers.refl _) cov) cov
  simp only [State.withRegions_withRegions] at run'
  exact ⟨tr1 ++ tr2, w, t, run', run, pre, st, mt, rf⟩

theorem slot_disj {σ : State} (pre : In (mkP s) σ) {lo n : Nat} (h1 : 4 ≤ lo) (h2 : lo + n ≤ 56) :
    ∀ r ∈ (mkP s).chg, Region.Disjoint ⟨State.addr (mkP s).sp + BitVec.ofNat 64 lo, n⟩ r := by
  have spf := pre.spFit
  intro r hr
  simp only [CP.chg, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact pre.sF.symm.sub_left (Offset.sub_base _ (by omega))
  · exact pre.oF.symm.sub_left (Offset.sub_base _ (by omega))
  · exact pre.uF.symm.sub_left (Offset.sub_base _ (by omega))
  · rw [pre.rC_eq]; exact Offset.disjoint_below _ (by omega)
  · exact Offset.disjoint_base _ (by omega) (by omega)

/-- A call's result. -/
theorem cand_ok [VG.Proof.Rsa.Arm.Keys.InvLaw] (v : RoundImpl) (h : CIn s) :
    WP isa (code v.name v.code) s fun t => abiPreserved s t ∧ CPost s t := by
  have spLo := h.spLo; have spHi := h.spHi
  have spN : (s.sp - BitVec.ofNat 32 56).toNat = s.sp.toNat - 56 := FrameStack.sub_toNat' (by omega)
  unfold code
  refine WP.frame (by decide) (by simp only [List.length_cons, List.length_nil]; omega) (by decide) ?_
  rw [WP.seq_iff]
  obtain ⟨tr, w, t, run', -, pre, st, mt, ⟨_, bk, r0, outs, used⟩⟩ := body_wide v h
  refine WP.mono (Q := fun x => x = w.withRegions s.rd (pcPushed s).wr) ⟨tr, _, run', rfl⟩ ?_
  rintro _ rfl
  have wsp : w.sp = s.sp - BitVec.ofNat 32 56 := bk.sp.trans st
  have spf := pre.spFit
  have w48 : Frame [⟨off (State.addr (mkP s).sp) 48, 4⟩] (pcPushed s).mem t.mem := by
    rw [mt]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have fr : Frame (⟨off (State.addr (mkP s).sp) 48, 4⟩ :: (mkP s).chg) (pcPushed s).mem w.mem :=
    (w48.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self).trans
      (bk.frame.mono fun r hr => List.mem_cons_of_mem _ hr)
  have sv := pc_push_callee_saved s (by omega)
  have s1 : Spill.Saved w.mem (State.addr (s.sp - 56)) s.gpr
      [(.r4, 16), (.r5, 20), (.r6, 24), (.r7, 28), (.r8, 32), (.r9, 36), (.r10, 40), (.r11, 44)] :=
    Spill.Saved.frame (lo := 16) (hi := 48) (fun p hp => sv p (by revert hp; revert p; decide)) (by decide) fr
      fun r hr => by
        rcases List.mem_cons.mp hr with rfl | hr
        · exact Offset.disjoint _ (.inl (by decide)) (by omega) (by omega)
        · exact slot_disj pre (by decide) (by decide) r hr
  have s2 : Spill.Saved w.mem (State.addr (s.sp - 56)) s.gpr [(.lr, 52)] :=
    Spill.Saved.frame (lo := 52) (hi := 56) (fun p hp => sv p (by revert hp; revert p; decide)) (by decide) fr
      fun r hr => by
        rcases List.mem_cons.mp hr with rfl | hr
        · exact Offset.disjoint _ (.inr (by decide)) (by omega) (by omega)
        · exact slot_disj pre (by decide) (by decide) r hr
  have saved : Spill.Saved w.mem (State.addr (s.sp - 56)) s.gpr pcCalleeSaved := fun p hp => by
    have hp' : p ∈ [(Reg.r4, 16), (.r5, 20), (.r6, 24), (.r7, 28), (.r8, 32), (.r9, 36), (.r10, 40), (.r11, 44)] ∨
        p ∈ [(Reg.lr, 52)] := by revert hp; revert p; decide
    rcases hp' with hp' | hp'
    exacts [s1 p hp', s2 p hp']
  have fit : (w.withRegions s.rd (pcPushed s).wr).sp.toNat + 56 ≤ 2 ^ 32 := by
    show w.sp.toNat + 56 ≤ _; rw [wsp, spN]; omega
  have read : InRegions ((w.withRegions s.rd (pcPushed s).wr).rd ++ (w.withRegions s.rd (pcPushed s).wr).wr)
      (State.addr (w.withRegions s.rd (pcPushed s).wr).sp) 56 := by
    have m : (⟨State.addr (s.sp - BitVec.ofNat 32 56), 56⟩ : Region) ∈ (w.withRegions s.rd (pcPushed s).wr).wr := by
      rw [State.withRegions_wr]; exact List.mem_cons_self
    refine ⟨_, List.mem_append_right _ m, ?_⟩
    rw [State.withRegions_sp, wsp]; exact Region.contains_self _ _
  refine WP.mono (pc_restore_ok _ s.gpr fit read (by rw [State.withRegions_sp, wsp]; exact saved)) ?_
  rintro t' ⟨restored, memT, restT⟩
  have ret : t'.gpr .r0 = w.gpr .r0 := restT.gpr .r0 (by simp [pcCalleeSaved])
  have rc := res_c h mt
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
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
  · rw [popped_sp, restT.sp, State.withRegions_sp, wsp]
    exact BitVec.sub_add_cancel _ _
  · rw [popped_gpr (by decide : Reg.r0 ≠ .r12), ret, r0]; unfold stR; rw [rc]
  · rw [popped_mem, memT, State.withRegions_mem]
    exact outs.trans (by unfold outR; rw [rc]; rfl)
  · rw [popped_mem, memT, State.withRegions_mem]
    exact used.trans (by unfold usedR; rw [rc]; rfl)

end

end VG.Proof.RsaKeyGen.Arm.Cand
