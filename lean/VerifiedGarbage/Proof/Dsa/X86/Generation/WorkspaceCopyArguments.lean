module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.PShape
public import VerifiedGarbage.Proof.Dsa.X86.Generation.QArguments
public import VerifiedGarbage.Proof.Mont.X86.Instr

/-! Point the shared byte-copy setup at the generation workspace. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Impl.Dsa.X86.Generation VG.Proof.Mont.X86

theorem workspace_copy_arguments {s : State} (source destination len : Nat) :
    WP isa (.block (workspaceCopyArguments source destination len)) s fun t =>
      t.gpr .esi = s.gpr .edi + BitVec.ofNat 32 source ∧
      t.gpr .ebx = s.gpr .edi + BitVec.ofNat 32 destination ∧
      t.gpr .ecx = BitVec.ofNat 32 len ∧ t.mem = s.mem ∧ Keeps [.ebp, .esi, .ebx, .ecx] s t := by
  unfold workspaceCopyArguments
  refine wp_movS rfl fun a A _ => ?_
  refine WP.mono (q_arguments (digestOffset := source) (candidateOffset := destination) (len := len) A.gpr)
    fun t ⟨src, dst, count, memory, K⟩ => ?_
  exact ⟨src, dst, count, memory.trans A.mem, (A.keeps.mono (by decide)).trans (K.mono (by decide))⟩

end VG.Proof.Dsa.X86.Generation
