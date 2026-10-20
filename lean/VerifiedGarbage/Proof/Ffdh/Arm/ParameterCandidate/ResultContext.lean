module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SavedFrame
public import VerifiedGarbage.Proof.Ffdh.Arm.Output
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! The final output and complete u64 consumption word have separate writable buffers. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm
open VG.Proof.Ffdh.Arm (OutputBuffer)

def resultValues (dst usedPtr : BitVec 32) (n consumed : Nat) : Nat → BitVec 32
  | 4 => dst
  | 12 => BitVec.ofNat 32 n
  | 32 => usedPtr
  | 40 => BitVec.ofNat 32 consumed
  | _ => 0

def resultSlots : List Nat := [4, 12, 32, 40]

structure ResultContext (dst usedPtr : BitVec 32) (n consumed : Nat) (s : State) : Prop where
  saved : SavedFrame (resultValues dst usedPtr n consumed) resultSlots s
  output : OutputBuffer dst n s
  used : OutputBuffer usedPtr 8 s
  positive : 0 < n
  countFits : n < 2 ^ 32
  consumedFits : consumed < 2 ^ 32
  outputStack : (⟨State.addr dst, n⟩ : Region).Disjoint ⟨State.addr s.sp, 72⟩
  usedStack : (⟨State.addr usedPtr, 8⟩ : Region).Disjoint ⟨State.addr s.sp, 72⟩
  outputUsed : (⟨State.addr dst, n⟩ : Region).Disjoint ⟨State.addr usedPtr, 8⟩

theorem ResultContext.after_output {s t : State} {dst usedPtr : BitVec 32} {n consumed : Nat} {rs : List Reg}
    (h : ResultContext dst usedPtr n consumed s) (changed : Frame [⟨State.addr dst, n⟩] s.mem t.mem)
    (rest : Rest rs s t) : ResultContext dst usedPtr n consumed t := by
  refine ⟨h.saved.after_output (by
    intro d hd
    simp only [resultSlots, List.mem_cons, List.not_mem_nil, or_false] at hd
    omega) changed rest h.outputStack,
    h.output.after rest, h.used.after rest, h.positive, h.countFits, h.consumedFits, ?_, ?_, h.outputUsed⟩
  · rw [rest.sp]; exact h.outputStack
  · rw [rest.sp]; exact h.usedStack

theorem ResultContext.after_memory {s t : State} {dst usedPtr : BitVec 32} {n consumed : Nat} {rs : List Reg}
    (h : ResultContext dst usedPtr n consumed s) (memory : t.mem = s.mem) (rest : Rest rs s t) :
    ResultContext dst usedPtr n consumed t := h.after_output (by rw [memory]; exact Frame.refl _ _) rest

end VG.Proof.Ffdh.Arm.ParameterCandidate
