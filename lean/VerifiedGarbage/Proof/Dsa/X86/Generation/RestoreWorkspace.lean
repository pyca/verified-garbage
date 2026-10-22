module

import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Framework.X86.Call
public import Init.Data.BitVec.Basic
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Mont.X86.Words

/-! Restore a workspace pointer saved above a borrowed arithmetic or hash frame. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont.X86

theorem restore_workspace {s u : State} {areas : List Region}
    (low : 4 ≤ (s.gpr .esp).toNat)
    (stack : u.gpr .esp = (pushed [.edi] s).gpr .esp)
    (rd : u.rd = (pushed [.edi] s).rd) (wr : u.wr = (pushed [.edi] s).wr)
    (F : Frame areas (pushed [.edi] s).mem u.mem)
    (apart : ∀ region ∈ areas, Region.Disjoint
      ⟨((pushed [.edi] s).gpr .esp).setWidth 64, 4⟩ region) :
    Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s (popped .edi 1 u) ∧
      Frame (below (s.gpr .esp) 4 :: areas) s.mem (popped .edi 1 u).mem := by
  have saved : u.mem.readW (((pushed [.edi] s).gpr .esp).setWidth 64) 32 = s.gpr .edi := by
    rw [F.readW (r := ⟨((pushed [.edi] s).gpr .esp).setWidth 64, 4⟩)
      (Region.contains_self _ _) apart (by decide)]
    simpa using pushed_word (rs := [.edi]) (s := s) (by decide)
      (by simpa only [List.length_cons, List.length_nil] using low) (i := 0) (by decide)
  have edi : (popped .edi 1 u).gpr .edi = s.gpr .edi := by
    have pop : (popped .edi 1 u).gpr .edi = u.mem.readW ((u.gpr .esp).setWidth 64) 32 := by
      simp only [popped, popReg, State.setReg, reduceCtorEq, ite_false, ite_true]
    rw [pop, stack, saved]
  have esp : (popped .edi 1 u).gpr .esp = s.gpr .esp := by
    rw [popped_esp, stack, pushed_esp]
    exact BitVec.sub_add_cancel _ _
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro reg hr
    have only : reg = .edi ∨ reg = .esp := by cases reg <;> simp_all
    rcases only with rfl | rfl
    · exact edi
    · exact esp
  · rw [popped_rd, rd, pushed_rd]
  · rw [popped_wr, wr, pushed_wr]; rfl
  · rw [popped_mem]
    exact ((pushed_frame (s := s) (rs := [.edi]) (by decide)
      (by simpa only [List.length_cons, List.length_nil] using low)).mono
        (by intro r hr; rw [List.mem_singleton.mp hr]; exact List.mem_cons_self ..)).trans
      (F.mono (by intro r hr; exact List.mem_cons_of_mem _ hr))

end VG.Proof.Dsa.X86.Generation
