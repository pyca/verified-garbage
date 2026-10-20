module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.LeafCT
import VerifiedGarbage.Proof.Dsa.X86.BytesTiming
import VerifiedGarbage.Proof.Dsa.X86.Generation.LoadStructure
import VerifiedGarbage.Proof.Framework.X86.RelCT

/-! # Component loading retains the public stack pointer for subsequent frame accesses -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86

theorem loadComponent_frame_ct (len n out : Nat) : RelCT isa (RegistersAgree [.edi, .esi, .esp])
    (VG.Impl.Dsa.X86.loadComponent len n out) (RegistersAgree [.edi, .esp]) := by
  intro s t ts tt s' t' R es et
  have A : VG.X86.Taint.Agree (VG.Proof.Mont.X86.Dynamic.workspaceTaint true) s t :=
    agree_regs (fun r hr => R r (by simpa using List.mem_append_left [Reg.esp] hr))
  obtain ⟨trace, B⟩ := loadComponent_relCT len n out _ _ _ _ _ _ A es et
  refine ⟨trace, ?_⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact B.rf.1 .edi (by decide)
  · rw [Exec.gpr (loadComponent_noSp len n out) es, Exec.gpr (loadComponent_noSp len n out) et]
    exact R .esp (by simp)
end VG.Proof.Dsa.X86.Generation
