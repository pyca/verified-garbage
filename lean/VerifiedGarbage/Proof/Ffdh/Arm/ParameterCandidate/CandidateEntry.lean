module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.EntryContext
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SavedProject
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Snapshot all candidate API arguments, including a zero count for short tapes. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.X25519.Arm

theorem candidateEntry_ok {s : State} {p : CandidateParams}
    (stack : Workspace s s.sp 72) (incoming : CandidateIncoming p s)
    (out : s.gpr .r0 = p.out) (width : s.gpr .r1 = BitVec.ofNat 32 p.length)
    (used : s.gpr .r2 = p.usedPtr) (bits : s.gpr .r3 = BitVec.ofNat 32 p.bits) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.entry) s fun t =>
      SavedFrame (candidateValues p 0) candidateSlots t ∧
      Frame [⟨State.addr s.sp, 72⟩] s.mem t.mem ∧ Rest [.r0, .r12] s t := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.entry
  refine wp_stackAddr (by decide) fun s0 moved => ?_
  obtain rest0 : Rest [.r12] s s0 := moved.rest (by simp)
  obtain frame0 : Frame [⟨State.addr s.sp, 72⟩] s.mem s0.mem := by rw [moved.mem]; exact Frame.refl _ _
  obtain context0 : EntryContext p [] s0 :=
    ⟨⟨by rw [rest0.sp]; exact stack.congr rest0.wr, by simp⟩, incoming.after frame0 rest0,
      by rw [moved.gpr, moved.sp, BitVec.add_zero]⟩
  refine wp_entryStore (r := .r0) context0 (by decide) (d := 4) (by decide) (by decide)
    ((rest0.gpr .r0 (by simp)).trans out) fun s1 context1 frame1 rest1 => ?_
  obtain kept1 := rest0.trans (rest1.mono (by simp))
  rw [rest0.sp] at frame1
  obtain changed1 := frame0.trans frame1
  refine wp_entryStore (r := .r0) context1 (by decide) (d := 8) (by decide) (by decide)
    ((kept1.gpr .r0 (by simp)).trans out) fun s2 context2 frame2 rest2 => ?_
  obtain kept2 := kept1.trans (rest2.mono (by simp))
  rw [kept1.sp] at frame2
  obtain changed2 := changed1.trans frame2
  refine wp_entryStore (r := .r1) context2 (by decide) (d := 12) (by decide) (by decide)
    ((kept2.gpr .r1 (by simp)).trans width) fun s3 context3 frame3 rest3 => ?_
  obtain kept3 := kept2.trans (rest3.mono (by simp))
  rw [kept2.sp] at frame3
  obtain changed3 := changed2.trans frame3
  refine wp_entryStore (r := .r2) context3 (by decide) (d := 32) (by decide) (by decide)
    ((kept3.gpr .r2 (by simp)).trans used) fun s4 context4 frame4 rest4 => ?_
  obtain kept4 := kept3.trans (rest4.mono (by simp))
  rw [kept3.sp] at frame4
  obtain changed4 := changed3.trans frame4
  refine wp_entryStore (r := .r3) context4 (by decide) (d := 24) (by decide) (by decide)
    ((kept4.gpr .r3 (by simp)).trans bits) fun s5 context5 frame5 rest5 => ?_
  obtain kept5 : Rest [.r0, .r12] s s5 := (kept4.trans (rest5.mono (by simp))).mono (by simp)
  rw [kept4.sp] at frame5
  obtain changed5 := changed4.trans frame5
  refine wp_entryCopy context5 (by decide) (i := 0) (d := 28) (by decide) (by decide) (by decide) rfl fun s6 context6 frame6 rest6 => ?_
  obtain kept6 := kept5.trans (rest6.mono (by simp))
  rw [kept5.sp] at frame6
  obtain changed6 := changed5.trans frame6
  refine wp_entryCopy context6 (by decide) (i := 1) (d := 16) (by decide) (by decide) (by decide) rfl fun s7 context7 frame7 rest7 => ?_
  obtain kept7 := kept6.trans (rest7.mono (by simp))
  rw [kept6.sp] at frame7
  obtain changed7 := changed6.trans frame7
  refine wp_entryCopy context7 (by decide) (i := 2) (d := 20) (by decide) (by decide) (by decide) rfl fun s8 context8 frame8 rest8 => ?_
  obtain kept8 := kept7.trans (rest8.mono (by simp))
  rw [kept7.sp] at frame8
  obtain changed8 := changed7.trans frame8
  refine wp_entryCopy context8 (by decide) (i := 3) (d := 0) (by decide) (by decide) (by decide) rfl fun s9 context9 frame9 rest9 => ?_
  obtain kept9 := kept8.trans (rest9.mono (by simp))
  rw [kept8.sp] at frame9
  obtain changed9 := changed8.trans frame9
  refine wp_entryCopy context9 (by decide) (i := 4) (d := 36) (by decide) (by decide) (by decide) rfl fun s10 context10 frame10 rest10 => ?_
  obtain kept10 := kept9.trans (rest10.mono (by simp))
  rw [kept9.sp] at frame10
  obtain changed10 := changed9.trans frame10
  refine wp_mov (op2_imm (v := (0 : BitVec 32)) (by decide)) fun u zeroed => ?_
  obtain restZ : Rest [.r0] s10 u := zeroed.rest (by simp)
  obtain ctxZ := context10.after_memory zeroed.mem restZ (by simp)
  refine wp_entryStore (r := .r0) ctxZ (by decide) (d := 40) (by decide) (by decide) zeroed.gpr fun t contextT frameT restT => WP.block_nil ?_
  obtain finalRest := kept10.trans ((restZ.mono (by simp)).trans (restT.mono (by simp)))
  rw [zeroed.mem, restZ.sp, kept10.sp] at frameT
  refine ⟨contextT.saved.project ?_ (by intro d hd; rfl), changed10.trans frameT, finalRest⟩
  intro d hd
  simp only [candidateSlots, List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
  omega_using [hd]

end VG.Proof.Ffdh.Arm.ParameterCandidate
