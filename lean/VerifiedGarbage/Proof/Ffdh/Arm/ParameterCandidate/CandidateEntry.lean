module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SavedProject
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateParams
public import VerifiedGarbage.Proof.Ffdh.Arm.IncomingWord
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SavedFrame
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! ### `Ffdh.Arm.ParameterCandidate.EntryContext`, which this module and modules that import it used -/

section

/-! Initialize the candidate's public arguments in the AAPCS local frame. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/SavedInstall.lean`, which only this module imported.
section

/-! Install entry arguments one at a time, preserving previously initialized slots. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.X25519.Arm

def validSavedSlots (slots : List Nat) : Bool := slots.all fun d => d % 4 == 0 && decide (d + 4 ≤ 72)

theorem SavedFrame.install {s t : State} {values : Nat → BitVec 32} {slots : List Nat} {d : Nat}
    {rs : List Reg} (h : SavedFrame values slots s) (valid : validSavedSlots slots = true)
    (aligned : d % 4 = 0) (fit : d + 4 ≤ 72)
    (memory : t.mem = s.mem.writeW (State.addr (s.sp + BitVec.ofNat 32 d)) (values d))
    (rest : Rest rs s t) : SavedFrame values (d :: slots) t := by
  refine ⟨by rw [rest.sp]; exact h.space.congr rest.wr, ?_⟩
  intro e he
  rw [rest.sp, memory]
  by_cases same : e = d
  · subst e
    exact Mem.readW_writeW_self32 _ _ _
  · have old : e ∈ slots := (List.mem_cons.mp he).resolve_left same
    have bounds := List.all_eq_true.mp valid e old
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at bounds
    have separate : (⟨State.addr (s.sp + BitVec.ofNat 32 e), 4⟩ : Region).Disjoint
        ⟨State.addr (s.sp + BitVec.ofNat 32 d), 4⟩ := by
      rw [VG.Arm.addr_add (by have := h.space.nowrap; omega_using [bounds, this]), VG.Arm.addr_add (by have := h.space.nowrap; omega_using [fit, this])]
      exact Offset.disjoint _ (by omega_using [aligned, same, bounds]) (by omega_using [bounds]) (by omega_using [fit])
    rw [Mem.readW_writeW_sep (separate.sep (Region.contains_self _ 4) (Region.contains_self _ 4)) (by decide)]
    exact h.saved e old

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.Ffdh.Arm (IncomingWord wp_load_incoming)

def candidateIncomingValue (p : CandidateParams) : Nat → BitVec 32
  | 0 => BitVec.ofNat 32 p.generator
  | 1 => p.tape
  | 2 => BitVec.ofNat 32 p.bytes.length
  | 3 => p.base
  | _ => BitVec.ofNat 32 p.capacity

structure CandidateIncoming (p : CandidateParams) (s : State) : Prop where
  word : ∀ i < 5, IncomingWord (candidateIncomingValue p i) (128 + 4 * i) s

theorem CandidateIncoming.after {s t : State} {p : CandidateParams} {rs : List Reg}
    (h : CandidateIncoming p s) (changed : Frame [⟨State.addr s.sp, 72⟩] s.mem t.mem) (rest : Rest rs s t) :
    CandidateIncoming p t := ⟨fun i hi => (h.word i hi).after (by omega_using []) changed rest⟩

structure EntryContext (p : CandidateParams) (slots : List Nat) (s : State) : Prop where
  saved : SavedFrame (candidateValues p 0) slots s
  incoming : CandidateIncoming p s
  pointer : s.gpr .r12 = s.sp

theorem EntryContext.after_memory {s t : State} {p : CandidateParams} {slots : List Nat} {rs : List Reg}
    (h : EntryContext p slots s) (memory : t.mem = s.mem) (rest : Rest rs s t) (kept : .r12 ∉ rs) :
    EntryContext p slots t :=
  ⟨h.saved.after_memory memory rest, h.incoming.after (by rw [memory]; exact Frame.refl _ _) rest,
    (rest.gpr .r12 kept).trans (h.pointer.trans rest.sp.symm)⟩

theorem wp_entryStore {s : State} {p : CandidateParams} {slots : List Nat} {d : Nat} {r : Reg}
    {is : List Instr} {Q : State → Prop} (h : EntryContext p slots s) (valid : validSavedSlots slots = true)
    (aligned : d % 4 = 0) (fit : d + 4 ≤ 72) (value : s.gpr r = candidateValues p 0 d)
    (next : ∀ t, EntryContext p (d :: slots) t → Frame [⟨State.addr s.sp, 72⟩] s.mem t.mem →
      Rest [] s t → WP isa (.block is) t Q) :
    WP isa (.block (.str r .r12 d :: is)) s Q := by
  have write : InRegions s.wr (State.addr (s.sp + BitVec.ofNat 32 d)) 4 := by
    rw [VG.Arm.addr_add (by have := h.saved.space.nowrap; omega_using [fit, this])]
    exact h.saved.space.write fit
  refine wp_str (a := State.addr (s.sp + BitVec.ofNat 32 d)) (by omega_using [fit]) (by rw [h.pointer]) write fun t stored => ?_
  have memory : t.mem = s.mem.writeW (State.addr (s.sp + BitVec.ofNat 32 d)) (candidateValues p 0 d) := by
    rw [stored.mem, value]
  have rest := stored.rest []
  have frame : Frame [⟨State.addr s.sp, 72⟩] s.mem t.mem := by
    rw [memory]
    refine (Frame.refl _ _).writeW (r := ⟨State.addr s.sp, 72⟩) (by simp) _ ?_
    rw [VG.Arm.addr_add (by have := h.saved.space.nowrap; omega_using [fit, this])]
    exact Offset.contains_base _ fit (by omega_using [fit])
  exact next t ⟨h.saved.install valid aligned fit memory rest, h.incoming.after frame rest,
    (rest.gpr .r12 (by simp)).trans (h.pointer.trans rest.sp.symm)⟩ frame rest

theorem wp_entryCopy {s : State} {p : CandidateParams} {slots : List Nat} {i d : Nat}
    {is : List Instr} {Q : State → Prop} (h : EntryContext p slots s) (valid : validSavedSlots slots = true)
    (index : i < 5) (aligned : d % 4 = 0) (fit : d + 4 ≤ 72)
    (equal : candidateIncomingValue p i = candidateValues p 0 d)
    (next : ∀ t, EntryContext p (d :: slots) t → Frame [⟨State.addr s.sp, 72⟩] s.mem t.mem →
      Rest [.r0] s t → WP isa (.block is) t Q) :
    WP isa (.block (.ldrSp .r0 (128 + 4 * i) :: .str .r0 .r12 d :: is)) s Q := by
  refine wp_load_incoming .r0 (h.incoming.word i index) (by omega_using [index]) fun u value memory rest => ?_
  have context := h.after_memory memory rest (by simp)
  refine wp_entryStore context valid aligned fit (value.trans equal) fun t contextT frameT restT => ?_
  rw [memory, rest.sp] at frameT
  exact next t contextT frameT (rest.trans (restT.mono (by simp)))

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

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
