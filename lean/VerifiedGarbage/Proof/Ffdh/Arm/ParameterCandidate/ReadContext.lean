module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SavedFrame
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialValue
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! Read-only candidate arguments shared by the residue checks and sieve. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm VG.Proof.Mont

def readValues (dst : BitVec 32) (n : Nat) : Nat → BitVec 32
  | 4 => dst
  | 12 => BitVec.ofNat 32 n
  | _ => 0

structure ReadContext (dst : BitVec 32) (n : Nat) (s : State) : Prop where
  frame : SavedFrame (readValues dst n) [4, 12] s
  positive : 0 < n
  countFits : n < 2 ^ 32
  bufferFits : dst.toNat + n ≤ 2 ^ 32
  readable : TrialReadable s (dst + BitVec.ofNat 32 n) n

theorem ReadContext.out {dst : BitVec 32} {n : Nat} {s : State} (h : ReadContext dst n s) :
    s.mem.readW (State.addr (s.sp + 4)) 32 = dst := h.frame.saved 4 (by simp)

theorem ReadContext.width {dst : BitVec 32} {n : Nat} {s : State} (h : ReadContext dst n s) :
    s.mem.readW (State.addr (s.sp + 12)) 32 = BitVec.ofNat 32 n := h.frame.saved 12 (by simp)

theorem ReadContext.after_memory {dst : BitVec 32} {n : Nat} {s t : State} {rs : List Reg}
    (h : ReadContext dst n s) (memory : t.mem = s.mem) (rest : Rest rs s t) : ReadContext dst n t := by
  refine ⟨h.frame.after_memory memory rest, h.positive, h.countFits, h.bufferFits, ?_⟩
  intro i hi
  rw [rest.rd, rest.wr]
  exact h.readable i hi

theorem ReadContext.lastAddress {dst : BitVec 32} {n : Nat} {s : State}
    (h : ReadContext dst n s) :
    State.addr (dst + BitVec.ofNat 32 n - 1) = off (State.addr dst) (n - 1) := by
  have subtract : BitVec.ofNat 32 n - BitVec.ofNat 32 1 = BitVec.ofNat 32 (n - 1) :=
    BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) h.positive
  have add : dst + BitVec.ofNat 32 n - 1 = dst + (BitVec.ofNat 32 n - BitVec.ofNat 32 1) := by
    change dst + BitVec.ofNat 32 n - 1#32 = _
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
  rw [add, subtract, VG.Arm.addr_add (by have := h.bufferFits; have := h.positive; omega)]

end VG.Proof.Ffdh.Arm.ParameterCandidate
