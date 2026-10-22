module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.QShape
public import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Impl.Dsa.X86.Generation.QShape
meta import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Proof.Framework.X86.Taint

/-! # Candidate shaping's addresses and loop count depend only on public pointers and length -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86

private theorem certificate : ∃ hc, (VG.Taint.check taint (τr [.esi, .ebx, .ecx])
    Impl.Dsa.X86.Generation.qShape hc).isSome = true := ⟨_, by taint_decide⟩

theorem q_shape_ct : RelCT isa
    (fun s t => s.gpr .esi = t.gpr .esi ∧ s.gpr .ebx = t.gpr .ebx ∧ s.gpr .ecx = t.gpr .ecx)
    Impl.Dsa.X86.Generation.qShape (fun _ _ => True) := by
  obtain ⟨hc, checked⟩ := certificate
  apply RelCT.taint (A := taint) (τr [.esi, .ebx, .ecx]) _ checked
  rintro s t ⟨source, dest, count⟩
  apply agree_regs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact source
  · exact dest
  · exact count

end VG.Proof.Dsa.X86.Generation
