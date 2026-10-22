module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialReady
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! Restore the saved workspace pointer after the shared filter borrows its registers. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

abbrev trialReturned (s : State) : State := popped .edi 1 (freed 36 s)
def trialCallerClob : List Reg := [.eax, .ebx, .ecx, .edx, .esi, .ebp]

theorem trial_saved_address {s : State} (low : 40 ≤ (s.gpr .esp).toNat) :
    ((pushed [.edi] s).gpr .esp).setWidth 64 = ((trialAllocated s).gpr .esp).setWidth 64 + 36#64 := by
  rw [trial_allocated_sp, pushed_esp]
  change (s.gpr .esp - 4#32).setWidth 64 = (s.gpr .esp - 40#32).setWidth 64 + 36#64
  rw [Taint.sub_setWidth (by omega : 4 ≤ (s.gpr .esp).toNat), Taint.sub_setWidth low,
    show (40#64 : BitVec 64) = 4#64 + 36#64 from rfl, ← BitVec.sub_sub, BitVec.sub_add_cancel]

theorem trial_return {s u : State} (low : 40 ≤ (s.gpr .esp).toNat)
    (F : Frame [⟨((trialAllocated s).gpr .esp).setWidth 64, 36⟩] (trialAllocated s).mem u.mem)
    (K : Keeps trialLoopClob (trialAllocated s) u) :
    Keeps trialCallerClob s (trialReturned u) ∧ Frame [below (s.gpr .esp) 40] s.mem (trialReturned u).mem ∧
      (trialReturned u).gpr .eax = u.gpr .eax := by
  have stack : u.gpr .esp = (trialAllocated s).gpr .esp := K.1 .esp (by decide)
  have outer : (freed 36 u).gpr .esp = (pushed [.edi] s).gpr .esp := by
    rw [freed_esp, stack, allocFrame_esp, BitVec.sub_add_cancel]
  have saved : u.mem.readW (((pushed [.edi] s).gpr .esp).setWidth 64) 32 = s.gpr .edi := by
    rw [F.readW (r := ⟨((pushed [.edi] s).gpr .esp).setWidth 64, 4⟩) (Region.contains_self _ _)
      (by
        intro r hr
        rw [List.mem_singleton.mp hr, trial_saved_address low]
        exact Offset.disjoint_base _ (by decide : 36 ≤ 36) (by decide : 36 + 4 ≤ 2 ^ 64)) (by decide)]
    change (pushed [.edi] s).mem.readW (((pushed [.edi] s).gpr .esp).setWidth 64) 32 = _
    simpa using pushed_word (rs := [.edi]) (s := s) (by decide) (by change 4 ≤ (s.gpr .esp).toNat; omega)
      (i := 0) (by decide)
  have edi : (trialReturned u).gpr .edi = s.gpr .edi := by
    change (popped .edi 1 (freed 36 u)).gpr .edi = _
    have pop : (popped .edi 1 (freed 36 u)).gpr .edi =
        u.mem.readW (((freed 36 u).gpr .esp).setWidth 64) 32 := by
      simp only [popped, popReg, State.setReg, reduceCtorEq, ite_false, ite_true, freed_mem]
    rw [pop, outer, saved]
  have esp : (trialReturned u).gpr .esp = s.gpr .esp := by
    rw [popped_esp, freed_esp, stack, trial_allocated_sp, BitVec.add_assoc]
    change s.gpr .esp - 40#32 + 40#32 = s.gpr .esp
    exact BitVec.sub_add_cancel _ _
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro r hr
    have register : r = .edi ∨ r = .esp := by cases r <;> simp_all [trialCallerClob]
    rcases register with rfl | rfl
    · exact edi
    · exact esp
  · rw [popped_rd, freed_rd, K.2.1, allocFrame_rd, pushed_rd]
  · rw [popped_wr, freed_wr, K.2.2, allocFrame_wr, pushed_wr]; rfl
  · rw [popped_mem, freed_mem]
    have first : Frame [below (s.gpr .esp) 40] s.mem (trialAllocated s).mem := by
      apply (pushed_frame (s := s) (rs := [.edi]) (by decide) (by change 4 ≤ (s.gpr .esp).toNat; omega)).sub
      intro r hr
      rw [List.mem_singleton.mp hr]
      exact ⟨_, List.mem_singleton_self _, below_sub (by decide) low⟩
    apply first.trans
    apply F.sub
    intro r hr
    rw [List.mem_singleton.mp hr, trial_allocated_sp]
    exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide : 36 ≤ 40)⟩
  · change (popped .edi 1 (freed 36 u)).gpr .eax = _
    rw [popped_gpr .edi 1 (freed 36 u) (by decide : Reg.eax ≠ .esp) (by decide : Reg.eax ≠ .edi),
      freed_gpr 36 u (by decide : Reg.eax ≠ .esp)]

end VG.Proof.Dsa.X86.Generation
