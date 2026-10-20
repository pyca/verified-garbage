module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.OuterBody
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameAllocation

/-! # The complete cdecl parameter generator meets the shared functional contract -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Dsa.X86.Generation

theorem code_ok (H : GenerationHashes) (F : KeyRandom.CheckCall.CheckFn) {s : State} (A : ParameterABI s) :
    WP isa (code H.sha1 H.sha256 F.name F.code) s fun t =>
      ∃ u, OuterFinished s u ∧ t = freed 16 u := by
  unfold code
  apply alloc_restored (by decide) (by have := A.stackLow; omega)
  exact WP.mono (outerBody_ok H F A) fun u result => ⟨result.esp, u, result, rfl⟩

theorem ParameterABI.returnApart {s : State} (A : ParameterABI s) :
    ∀ r ∈ outerWrites s, (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint r := by
  intro r hr
  simp only [outerWrites, entryWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [A.outerBase_eq]
    exact Offset.base_disjoint_below _ (by decide)
  · exact A.retScratch
  · exact A.retOut
  · exact (Offset.base_disjoint_below ((s.gpr .esp).setWidth 64) (n := 292) (k := 4)
      (by decide)).sub_right (Region.sub_prefix (by decide))

theorem generateParameters_correct (H : GenerationHashes) (F : KeyRandom.CheckCall.CheckFn)
    (s : State) (pre : (Spec.Dsa.generateParametersContract abi 292).pre s) :
    ∃ trace t, Exec isa (code H.sha1 H.sha256 F.name F.code) s trace t ∧ abiPreserved s t ∧
      (Spec.Dsa.generateParametersContract abi 292).post s t := by
  have A := parameterABI_of pre
  obtain ⟨trace, t, exec, u, result, rfl⟩ := code_ok H F A
  refine ⟨trace, _, exec, ⟨?_, ?_⟩, ?_⟩
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [freed_gpr _ _ (by decide)]; exact result.ebx
    · rw [freed_gpr _ _ (by decide)]; exact result.esi
    · rw [freed_gpr _ _ (by decide)]; exact result.edi
    · rw [freed_gpr _ _ (by decide)]; exact result.ebp
    · rw [freed_esp, result.esp, allocated_esp, BitVec.sub_add_cancel]
  · change u.mem.readW _ 32 = _
    exact result.frame.readW (Region.contains_self _ 4) A.returnApart (by decide)
  · sig_post [Spec.Dsa.generateParametersContract, Spec.Dsa.generateParametersSig, abi, argSlots, argVal, argBytes,
      stackBelow]
    refine ⟨?_, result.out⟩
    rw [BitVec.setWidth_append_eq_right]
    change (u.gpr .eax).toNat = Spec.Dsa.signStatus (parameterBytes s)
    rw [result.eax]
    cases parameterBytes s <;> rfl
end VG.Proof.Dsa.X86.Generation
