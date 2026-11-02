module

public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Top5
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Loads
public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Top1

/-! # DSA's probable-prime test on ARMv7: a call's result (`prime_ok`) -/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm VG.Arm.FrameStack VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.MillerRabin.Arm (RoundImpl)

section
variable {bits : Nat} {s : State}

/-- A call's result. -/
theorem prime_ok (v : RoundImpl) (h : CIn bits s) :
    WP isa (Impl.Dsa.Arm.ProbablePrime.code v.name v.code) s fun t => abiPreserved s t ∧ CPost bits s t := by
  have hb := h.sized
  have spLo := h.spLo; have spHi := h.spHi
  unfold Impl.Dsa.Arm.ProbablePrime.code
  refine WP.alloc (by decide) (by omega) ?_
  rw [WP.seq_iff]
  refine WP.mono (pre_ok hb spLo spHi h.argsIn h.arg) fun t ⟨rest, fr, vals, r1, r2⟩ => ?_
  have o : PreOut bits s t := ⟨rest, fr, vals, r1, r2⟩
  have tspN : t.sp.toNat = s.sp.toNat - 32 := by
    rw [rest.sp]; exact sub_toNat' (by omega)
  refine WP.frame (by decide) (by simp only [List.length_cons, List.length_nil]; omega) (by decide) ?_
  rw [WP.seq_iff]
  obtain ⟨tr, w, -, run', ⟨-, bk, r0, used⟩⟩ := body_wide v hb h o
  refine WP.mono (Q := fun x => x = w.withRegions s.rd (pcPushed t).wr) ⟨tr, _, run', rfl⟩ ?_
  rintro _ rfl
  have pre := bk.pre
  have wsp : w.sp = (mkP bits s).sp := bk.sp.trans pre.sp
  have spN : (mkP bits s).sp.toNat = s.sp.toNat - 88 := sub_toNat' (by omega)
  have sv := pc_push_callee_saved t (by omega)
  rw [show (t.sp - 56 : BitVec 32) = (mkP bits s).sp from pushed_sp o] at sv
  have saved : Spill.Saved w.mem (State.addr (mkP bits s).sp) t.gpr pcCalleeSaved := fun p hp => by
    have ho : FwOk p.2 := by revert hp; revert p; decide
    exact (bk.frame.readW (r := ⟨State.addr (mkP bits s).sp + BitVec.ofNat 64 p.2, 4⟩) (Region.contains_self _ _)
      (pre.fwSep ho) (by decide)).trans (sv p hp)
  have fit : (w.withRegions s.rd (pcPushed t).wr).sp.toNat + 56 ≤ 2 ^ 32 := by
    show w.sp.toNat + 56 ≤ _; rw [wsp, spN]; omega
  have read : InRegions ((w.withRegions s.rd (pcPushed t).wr).rd ++ (w.withRegions s.rd (pcPushed t).wr).wr)
      (State.addr (w.withRegions s.rd (pcPushed t).wr).sp) 56 := by
    refine ⟨⟨State.addr (mkP bits s).sp, 56⟩, List.mem_append_right _ ?_, ?_⟩
    · show _ ∈ ⟨State.addr (t.sp - BitVec.ofNat 32 56), 56⟩ :: t.wr
      rw [show t.sp - BitVec.ofNat 32 56 = (mkP bits s).sp from pushed_sp o]; exact List.mem_cons_self
    · rw [State.withRegions_sp, wsp]; exact Region.contains_self _ _
  refine WP.mono (pc_restore_ok _ t.gpr fit read (by rw [State.withRegions_sp, wsp]; exact saved)) ?_
  rintro t' ⟨restored, memT, restT⟩
  have rc := res_c pre
  have m' : t'.mem = w.mem := memT
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_, by show Proof.Dsa.ModPow.Keeps _ _ _ s.mem t'.mem; rw [m']; exact keeps h o bk, fun b rst hr => ?_⟩
  · have ne : r ≠ .r12 := by intro he; subst r; simp [preserved] at hr
    show (popped .r12 56 t').gpr r = _
    rw [popped_gpr ne]
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (restored (.r4, 16) (by simp [pcCalleeSaved])).trans (rest.gpr _ (by decide))
    · exact (restored (.r5, 20) (by simp [pcCalleeSaved])).trans (rest.gpr _ (by decide))
    · exact (restored (.r6, 24) (by simp [pcCalleeSaved])).trans (rest.gpr _ (by decide))
    · exact (restored (.r7, 28) (by simp [pcCalleeSaved])).trans (rest.gpr _ (by decide))
    · exact (restored (.r8, 32) (by simp [pcCalleeSaved])).trans (rest.gpr _ (by decide))
    · exact (restored (.r9, 36) (by simp [pcCalleeSaved])).trans (rest.gpr _ (by decide))
    · exact (restored (.r10, 40) (by simp [pcCalleeSaved])).trans (rest.gpr _ (by decide))
    · exact (restored (.r11, 44) (by simp [pcCalleeSaved])).trans (rest.gpr _ (by decide))
    · exact (restored (.lr, 52) (by simp [pcCalleeSaved])).trans (rest.gpr _ (by decide))
  · show t'.sp + BitVec.ofNat 32 56 + BitVec.ofNat 32 32 = s.sp
    rw [restT.sp, State.withRegions_sp, wsp]
    show s.sp - BitVec.ofNat 32 88 + BitVec.ofNat 32 56 + BitVec.ofNat 32 32 = s.sp
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.sub_add_cancel]
  · show ((popped .r12 56 t').gpr .r0).toNat = _
    rw [popped_gpr (by decide), restT.gpr .r0 (by simp [pcCalleeSaved]), State.withRegions_gpr, r0]
    unfold statD; rw [rc]
  · show Spec.Rsa.wordsAt t'.mem _ 1 = _
    rw [m']
    refine used.trans ?_
    unfold usedD; rw [rc, hr]; rfl

end

end VG.Proof.Dsa.Arm.Prime
