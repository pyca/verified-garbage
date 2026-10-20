module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Push
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Bounds
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Geometry
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Regions
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! The caller's nine ARM stack arguments are read above the saved search
frame and remain separate from the controller workspace. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Proof.Mont

theorem KeyInput.pushed_arguments {p : KeyPublic sampling} {s : State} (h : KeyInput p s) :
    EntryArguments p (searchPushed s) := by
  have fit : stackUse sampling ≤ s.sp.toNat := by have := h.bounds.stackFits; rw [← h.2.1] at this; exact this
  have argsFit : s.sp.toNat + argsBytes sampling ≤ 2 ^ 32 := by have := h.bounds.argsFit; rw [← h.2.1] at this; exact this
  have size := entryWords_bytes sampling
  have bytesBound : argsBytes sampling≤44 := by cases sampling <;> decide
  have positive : 24 ≤ stackUse sampling := by have := stackUse_min sampling; omega
  have native (i : Nat) (hi : i < entryWords sampling) : stackArgAddr s i = off (State.addr s.sp) (4 * i) :=
    VG.Arm.addr_add (by omega)
  have start : stackArgAddr s 0 = State.addr s.sp := by simp [stackArgAddr]
  have wholeRead : InRegions (s.rd ++ s.wr) (State.addr s.sp) (argsBytes sampling) := by
    refine ⟨inArgs sampling s, List.mem_append_left _ ?_, ?_⟩
    · rw [h.layout.rd]; simp [reads]
    · rw [inArgs, start]; exact Region.contains_self _ _
  have pushedFrame : Frame [FrameStack.belowA s.sp 24] s.mem (searchPushed s).mem :=
    FrameStack.pushed_frameA (rs := [.r4, .r9, .r10, .r11, .r12, .lr]) (by omega : 24 ≤ s.sp.toNat)
  have rootSp : p.sp = s.sp := by rw [← h.2.1]; rfl
  have savedSub : (FrameStack.belowA s.sp 24).Sub (FrameStack.belowA p.sp (stackUse sampling)) := by
    rw [rootSp]
    exact FrameStack.belowA_sub (by cases sampling <;> decide : 24 ≤ (stackUse sampling)) fit
  have argsSaved : (inArgs sampling s).Disjoint (FrameStack.belowA s.sp 24) :=
    ((h.stack_separate (r := inArgs sampling s) (List.mem_append_right s.wr (by rw [h.layout.rd]; simp [reads]))).sub_left savedSub).symm
  have argsControl : (inArgs sampling s).Disjoint ⟨State.addr p.control, 128⟩ := by
    rw [← h.2.1]
    exact (h.layout.separate (inControl s) (by simp [writes]) (inArgs sampling s) (by simp [reads])).symm
  have offsetAddress (i : Nat) (hi : i < entryWords sampling) :
      off (State.addr (searchPushed s).sp) (24 + 4 * i) = stackArgAddr s i := by
    have room : (searchPushed s).sp.toNat + (24 + 4 * i) < 2 ^ 32 := by
      change (s.sp - 24#32).toNat + (24 + 4 * i) < 2 ^ 32
      rw [FrameStack.sub_toNat' (by omega : 24 ≤ s.sp.toNat)]
      omega
    change State.addr (searchPushed s).sp + BitVec.ofNat 64 (24 + 4 * i) = _
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
      obtain ⟨r, hr, contains⟩ := CallLay.inRegions_sub wholeRead (by omega : 4 * i + 4 ≤ argsBytes sampling) (by omega)
      refine ⟨r, ?_, contains⟩
      rcases List.mem_append.mp hr with hr | hr
      · exact List.mem_append_left _ hr
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr)
    · rw [offsetAddress i hi]
      have sub : (⟨stackArgAddr s i, 4⟩ : Region).Sub (inArgs sampling s) := by
        rw [native i hi, inArgs, start]
        exact Offset.sub_base _ (by omega)
      have old := pushedFrame.readW (w := 32) (a := stackArgAddr s i) (r := ⟨stackArgAddr s i, 4⟩) (Region.contains_self _ _)
        (by simpa using argsSaved.sub_left sub) (by decide)
      exact old.trans (h.incoming_value hi)
  · intro i hi
    rw [offsetAddress i hi]
    apply argsControl.sub_left
    rw [native i hi, inArgs, start]
    exact Offset.sub_base _ (by omega)

end VG.Proof.Ffdh.Arm.KeySearch
