module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateParams
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SavedInstall
public import VerifiedGarbage.Proof.Ffdh.Arm.IncomingWord
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! Initialize the candidate's public arguments in the AAPCS local frame. -/

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
    CandidateIncoming p t := ⟨fun i hi => (h.word i hi).after (by omega) changed rest⟩

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
    rw [VG.Arm.addr_add (by have := h.saved.space.nowrap; omega)]
    exact h.saved.space.write fit
  refine wp_str (a := State.addr (s.sp + BitVec.ofNat 32 d)) (by omega) (by rw [h.pointer]) write fun t stored => ?_
  have memory : t.mem = s.mem.writeW (State.addr (s.sp + BitVec.ofNat 32 d)) (candidateValues p 0 d) := by
    rw [stored.mem, value]
  have rest := stored.rest []
  have frame : Frame [⟨State.addr s.sp, 72⟩] s.mem t.mem := by
    rw [memory]
    refine (Frame.refl _ _).writeW (r := ⟨State.addr s.sp, 72⟩) (by simp) _ ?_
    rw [VG.Arm.addr_add (by have := h.saved.space.nowrap; omega)]
    exact Offset.contains_base _ fit (by omega)
  exact next t ⟨h.saved.install valid aligned fit memory rest, h.incoming.after frame rest,
    (rest.gpr .r12 (by simp)).trans (h.pointer.trans rest.sp.symm)⟩ frame rest

theorem wp_entryCopy {s : State} {p : CandidateParams} {slots : List Nat} {i d : Nat}
    {is : List Instr} {Q : State → Prop} (h : EntryContext p slots s) (valid : validSavedSlots slots = true)
    (index : i < 5) (aligned : d % 4 = 0) (fit : d + 4 ≤ 72)
    (equal : candidateIncomingValue p i = candidateValues p 0 d)
    (next : ∀ t, EntryContext p (d :: slots) t → Frame [⟨State.addr s.sp, 72⟩] s.mem t.mem →
      Rest [.r0] s t → WP isa (.block is) t Q) :
    WP isa (.block (.ldrSp .r0 (128 + 4 * i) :: .str .r0 .r12 d :: is)) s Q := by
  refine wp_load_incoming .r0 (h.incoming.word i index) (by omega) fun u value memory rest => ?_
  have context := h.after_memory memory rest (by simp)
  refine wp_entryStore context valid aligned fit (value.trans equal) fun t contextT frameT restT => ?_
  rw [memory, rest.sp] at frameT
  exact next t contextT frameT (rest.trans (restT.mono (by simp)))

end VG.Proof.Ffdh.Arm.ParameterCandidate
