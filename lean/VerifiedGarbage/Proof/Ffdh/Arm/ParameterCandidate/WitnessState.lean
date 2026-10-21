module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.RoundData
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SavedFrame
public import VerifiedGarbage.Proof.Framework.Arm.CallF
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! Public phase state for rejection-sampled Miller–Rabin witnesses. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm

structure WitnessParams where
  base : BitVec 32
  tape : BitVec 32
  capacity : Nat
  words : Nat
  modulus : Nat
  bits : Nat
  checks : Nat
  bytes : List Byte

def witnessValues (p : WitnessParams) (used passed : Nat) : Nat → BitVec 32
  | 0 => p.base
  | 16 => p.tape
  | 20 => BitVec.ofNat 32 p.bytes.length
  | 36 => BitVec.ofNat 32 p.capacity
  | 40 => BitVec.ofNat 32 used
  | 44 => BitVec.ofNat 32 p.bits
  | 48 => BitVec.ofNat 32 ((p.bits + 7) / 8)
  | 52 => BitVec.ofNat 32 p.checks
  | 56 => BitVec.ofNat 32 passed
  | _ => 0

def witnessSlots : List Nat := [0, 16, 20, 36, 40, 44, 48, 52, 56]

def witnessRegions (p : WitnessParams) (sp : BitVec 32) : List Region :=
  [⟨State.addr p.base, 8 * p.capacity⟩, FrameStack.belowA sp 56,
    ⟨State.addr (sp + 40#32), 4⟩, ⟨State.addr (sp + 56#32), 4⟩]

structure WitnessState (p : WitnessParams) (used passed : Nat) (s : State) : Prop where
  data : RoundData p.base p.capacity p.words p.modulus s.mem
  workspace : Workspace s p.base (8 * p.capacity)
  saved : SavedFrame (witnessValues p used passed) witnessSlots s
  stackScratch : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr p.base, 8 * p.capacity⟩
  stackBelow : 56 ≤ s.sp.toNat
  belowScratch : (FrameStack.belowA s.sp 56).Disjoint ⟨State.addr p.base, 8 * p.capacity⟩
  bitsExact : p.bits = Spec.RsaKeyGen.bitLength (p.modulus - 1)
  bitsPositive : 0 < p.bits
  bitsBound : p.bits ≤ 8192
  bitsFit : p.bits ≤ 64 * p.words
  checksPositive : 0 < p.checks
  checksBound : p.checks ≤ 128
  usedBound : used ≤ p.bytes.length
  passedBound : passed ≤ p.checks
  tapeCount : p.bytes.length < 2 ^ 32
  tapeFits : p.tape.toNat + p.bytes.length ≤ 2 ^ 32
  tapeRead : InRegions (s.rd ++ s.wr) (State.addr p.tape) p.bytes.length
  tapeScratch : (⟨State.addr p.tape, p.bytes.length⟩ : Region).Disjoint ⟨State.addr p.base, 8 * p.capacity⟩
  tapeStack : (⟨State.addr p.tape, p.bytes.length⟩ : Region).Disjoint ⟨State.addr s.sp, 72⟩
  tapeBelow : (⟨State.addr p.tape, p.bytes.length⟩ : Region).Disjoint (FrameStack.belowA s.sp 56)
  tapeBytes : Spec.Rsa.bytesAt s.mem (State.addr p.tape) p.bytes.length = p.bytes

theorem witnessSlots_bound {d : Nat} (member : d ∈ witnessSlots) : d + 4 ≤ 72 := by
  simp only [witnessSlots, List.mem_cons, List.not_mem_nil, or_false] at member
  omega

theorem WitnessState.after_frame {s t : State} {p : WitnessParams} {used passed nextUsed nextPassed : Nat}
    {rs : List Reg} (h : WitnessState p used passed s)
    (data : RoundData p.base p.capacity p.words p.modulus t.mem)
    (saved : SavedFrame (witnessValues p nextUsed nextPassed) witnessSlots t)
    (usedBound : nextUsed ≤ p.bytes.length) (passedBound : nextPassed ≤ p.checks)
    (changed : Frame (witnessRegions p s.sp) s.mem t.mem) (rest : Rest rs s t) :
    WitnessState p nextUsed nextPassed t := by
  refine ⟨data, h.workspace.congr rest.wr, saved, ?_, ?_, ?_, h.bitsExact,
    h.bitsPositive, h.bitsBound, h.bitsFit, h.checksPositive, h.checksBound, usedBound, passedBound,
    h.tapeCount, h.tapeFits, ?_, h.tapeScratch, ?_, ?_, ?_⟩
  · rw [rest.sp]; exact h.stackScratch
  · rw [rest.sp]; exact h.stackBelow
  · rw [rest.sp]; exact h.belowScratch
  · rw [rest.rd, rest.wr]; exact h.tapeRead
  · rw [rest.sp]; exact h.tapeStack
  · rw [rest.sp]; exact h.tapeBelow
  · refine (rsa_bytes_frame changed (by have := h.tapeCount; omega) ?_).trans h.tapeBytes
    intro r hr
    simp only [witnessRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.tapeScratch
    · exact h.tapeBelow
    · rw [VG.Arm.addr_add (by have := h.saved.space.nowrap; omega)]
      exact h.tapeStack.sub_right (Offset.sub_base _ (by decide : 40 + 4 ≤ 72))
    · rw [VG.Arm.addr_add (by have := h.saved.space.nowrap; omega)]
      exact h.tapeStack.sub_right (Offset.sub_base _ (by decide : 56 + 4 ≤ 72))

theorem WitnessState.after_memory {s t : State} {p : WitnessParams} {used passed : Nat} {rs : List Reg}
    (h : WitnessState p used passed s) (memory : t.mem = s.mem) (rest : Rest rs s t) :
    WitnessState p used passed t := h.after_frame (memory ▸ h.data) (h.saved.after_memory memory rest)
      h.usedBound h.passedBound (by rw [memory]; exact Frame.refl _ _) rest

end VG.Proof.Ffdh.Arm.ParameterCandidate
