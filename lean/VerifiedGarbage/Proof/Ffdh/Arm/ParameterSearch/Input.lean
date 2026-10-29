module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Function
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Public
public import VerifiedGarbage.Spec.Ffdh.SievedContract

import VerifiedGarbage.Proof.Framework.Arm.Exec
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Nat
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Layout
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Incoming
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Push
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
/-! The unchanged public signature provides all inputs for the verified native search function. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterSearch/PushedArguments.lean`, which only this module imported.
section

/-! All six public ARM stack arguments survive the saved-register push and remain readable. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Mont

theorem SearchAbi.incoming_value {p : SearchParams} {s : State} (args : SearchAbi p s)
    {i : Nat} (bound : i < 6) : stackArg s i = incomingValue p i := by
  have choices : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
  rcases choices with rfl | rfl | rfl | rfl | rfl | rfl
  · exact args.generator
  · exact args.tape
  · exact args.tapeLength
  · exact args.base
  · exact args.capacity
  · exact args.control

theorem pushed_arguments {p : SearchParams} {s : State}
    (h : SearchLayout p s) (args : SearchAbi p s) : EntryArguments p (bodyState s) := by
  have fit := h.stackFits
  have argsFit := h.argsFits
  have native (i : Nat) (hi : i < 6) : stackArgAddr s i = off (State.addr s.sp) (4 * i) :=
    VG.Arm.addr_add (by omega)
  have wholeRead : InRegions (s.rd ++ s.wr) (State.addr s.sp) 24 :=
    ⟨_, List.mem_append_left _ (by rw [h.reads]; simp [readRegions]), Region.contains_self _ _⟩
  have pushedFrame : Frame [FrameStack.belowA s.sp 24] s.mem (bodyState s).mem :=
    FrameStack.pushed_frameA (rs := [.r4, .r9, .r10, .r11, .r12, .lr]) (by omega : 24 ≤ s.sp.toNat)
  have savedSub : (FrameStack.belowA s.sp 24).Sub (FrameStack.belowA s.sp 232) :=
    FrameStack.belowA_sub (by decide) fit
  have argsSaved : (⟨State.addr s.sp, 24⟩ : Region).Disjoint (FrameStack.belowA s.sp 24) :=
    ((h.stackSeparate _ (by simp [readRegions])).sub_left savedSub).symm
  have offsetAddress (i : Nat) (hi : i < 6) :
      off (State.addr (bodyState s).sp) (24 + 4 * i) = stackArgAddr s i := by
    have room : (bodyState s).sp.toNat + (24 + 4 * i) < 2 ^ 32 := by
      change (s.sp - 24#32).toNat + (24 + 4 * i) < 2 ^ 32
      rw [FrameStack.sub_toNat' (by omega : 24 ≤ s.sp.toNat)]
      omega
    change State.addr (bodyState s).sp + BitVec.ofNat 64 (24 + 4 * i) = _
    rw [← VG.Arm.addr_add room]
    change State.addr (s.sp - 24#32 + BitVec.ofNat 32 (24 + 4 * i)) = _
    rw [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]
    rfl
  refine ⟨?_, ?_⟩
  · intro i hi
    refine ⟨?_, ?_, ?_⟩
    · change (s.sp - 24#32).toNat + (24 + 4 * i) + 4 ≤ 2 ^ 32
      rw [FrameStack.sub_toNat' (by omega : 24 ≤ s.sp.toNat)]
      omega
    · rw [offsetAddress i hi, native i hi]
      obtain ⟨r, member, contains⟩ := CallLay.inRegions_sub wholeRead (by omega : 4 * i + 4 ≤ 24) (by decide)
      refine ⟨r, ?_, contains⟩
      rcases List.mem_append.mp member with read | write
      · exact List.mem_append_left _ (List.mem_cons_of_mem _ read)
      · exact List.mem_append_right _ write
    · rw [offsetAddress i hi]
      have sub : (⟨stackArgAddr s i, 4⟩ : Region).Sub ⟨State.addr s.sp, 24⟩ := by
        rw [native i hi]
        exact Offset.sub_base _ (by omega)
      exact (pushedFrame.readW (w := 32) (a := stackArgAddr s i) (r := ⟨stackArgAddr s i, 4⟩)
        (Region.contains_self _ _) (by simpa using argsSaved.sub_left sub) (by decide)).trans (args.incoming_value hi)
  · intro i hi
    rw [offsetAddress i hi]
    apply h.controlArgs.symm.sub_left
    rw [native i hi]
    exact Offset.sub_base _ (by omega)

end VG.Proof.Ffdh.Arm.ParameterSearch
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterSearch/PushMemory.lean`, which only this module imported.
section

/-! The native saved-register push preserves the entropy tape and every public policy word. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Mont

theorem SearchLayout.push_word {p : SearchParams} {s : State} (h : SearchLayout p s)
    {j : Nat} (bound : j < 16) :
    (bodyState s).mem.readW (off (State.addr p.control) (8 * j)) 64 =
      s.mem.readW (off (State.addr p.control) (8 * j)) 64 := by
  have frame : Frame [FrameStack.belowA s.sp 24] s.mem (bodyState s).mem :=
    FrameStack.pushed_frameA (rs := [.r4, .r9, .r10, .r11, .r12, .lr]) (by change 24 ≤ s.sp.toNat; have := h.stackFits; omega)
  have separate := (h.stackSeparate ⟨State.addr p.control, 128⟩ (by simp [writeRegions])).sub_left
    (FrameStack.belowA_sub (by decide : 24 ≤ 232) h.stackFits)
  exact frame.readW (r := ⟨State.addr p.control, 128⟩)
    (Offset.contains_base _ (by omega : 8 * j + 8 ≤ 128) (by omega))
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact separate.symm) (by decide)

theorem SearchLayout.push_bytes {p : SearchParams} {s : State} (h : SearchLayout p s)
    (args : SearchAbi p s) :
    Spec.Rsa.bytesAt (bodyState s).mem (State.addr p.c.tape) p.c.bytes.length = p.c.bytes := by
  have frame : Frame [FrameStack.belowA s.sp 24] s.mem (bodyState s).mem :=
    FrameStack.pushed_frameA (rs := [.r4, .r9, .r10, .r11, .r12, .lr]) (by change 24 ≤ s.sp.toNat; have := h.stackFits; omega)
  have separate := (h.stackSeparate ⟨State.addr p.c.tape, p.c.bytes.length⟩
    (by simp [readRegions])).sub_left (FrameStack.belowA_sub (by decide : 24 ≤ 232) h.stackFits)
  exact (VG.Proof.Bignum.Arm.rsa_bytes_frame frame (by have := p.c.tapeCount; omega)
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact separate.symm)).trans args.bytes

end VG.Proof.Ffdh.Arm.ParameterSearch
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Bignum.Arm

theorem searchInput {p : SearchParams} {s : State}
    (pre : (Spec.Ffdh.sievedParameterSearchContract abi 232).pre s) (args : SearchAbi p s) : FunctionInput p s := by
  have layout := searchLayout pre args
  have fit := layout.stackFits
  have savedSub : (⟨State.addr (bodyState s).sp, 24⟩ : Region).Sub (FrameStack.belowA s.sp 232) :=
    FrameStack.belowA_sub (by decide) fit
  have belowSub : (FrameStack.belowA (bodyState s).sp 208).Sub (FrameStack.belowA s.sp 232) :=
    FrameStack.belowA_inner (by decide) fit
  have storage : SearchBuffers p ((bodyState s).setReg .r4 p.control) := by
    refine ⟨⟨⟨p.controlFits, ?_⟩, ?_⟩, ⟨p.c.outputFits, ?_⟩, ⟨p.c.usedFits, ?_⟩,
      ⟨p.c.scratchFits, ?_⟩, ?_, layout.push_bytes args, ?_, ?_, ?_⟩
    · change (⟨State.addr p.control, 128⟩ : Region) ∈ s.wr
      rw [layout.writes]; simp [writeRegions]
    · simp only [State.setReg, ite_true]
    · change (⟨State.addr p.c.out, p.c.length⟩ : Region) ∈ s.wr
      rw [layout.writes]; simp [writeRegions]
    · change (⟨State.addr p.c.usedPtr, 8⟩ : Region) ∈ s.wr
      rw [layout.writes]; simp [writeRegions]
    · change (⟨State.addr p.c.base, 8 * p.c.capacity⟩ : Region) ∈ s.wr
      rw [layout.writes]; simp [writeRegions]
    · refine ⟨_, List.mem_append_left _ (List.mem_cons_of_mem _ ?_), Region.contains_self _ _⟩
      rw [layout.reads]; simp [readRegions]
    · exact ⟨_, List.mem_append_left _ (List.mem_cons_self), Region.contains_self _ _⟩
    · change 208 ≤ (s.sp - 24#32).toNat
      rw [FrameStack.sub_toNat' (by omega : 24 ≤ s.sp.toNat)]
      omega
    · intro r member
      have original : r ∈ writeRegions p ++ readRegions p s.sp := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl <;> simp [writeRegions, readRegions]
      exact ⟨(layout.stackSeparate r original).sub_left savedSub,
        (layout.stackSeparate r original).sub_left belowSub⟩
  have initial : SearchStart p (bodyState s) := by
    refine ⟨storage, pushed_arguments layout args, args.out, args.used, args.bits, ?_, ?_, ?_⟩
    · have word := layout.push_word (j := 0) (by decide)
      have address : VG.Proof.Mont.off (State.addr p.control) 0 = State.addr p.control := by simp [VG.Proof.Mont.off]
      rw [show 8 * 0 = 0 from rfl, address] at word
      exact word.trans args.counter
    · exact (layout.push_word (j := 1) (by decide)).trans args.widthPolicy
    · exact (layout.push_word (j := 2) (by decide)).trans args.entropyPolicy
  refine ⟨fit, initial, ?_⟩
  intro r member
  rw [layout.writes] at member
  exact (layout.stackSeparate r (List.mem_append_left _ member)).sub_left savedSub

end VG.Proof.Ffdh.Arm.ParameterSearch
