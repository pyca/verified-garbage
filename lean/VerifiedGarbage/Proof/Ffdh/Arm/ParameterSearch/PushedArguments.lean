module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Layout
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Incoming
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Push
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! All six public ARM stack arguments survive the saved-register push and remain readable. -/

@[expose] public section
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
