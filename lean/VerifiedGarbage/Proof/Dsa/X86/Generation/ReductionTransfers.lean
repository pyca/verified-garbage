module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.PReduce
public import VerifiedGarbage.Proof.Dsa.X86.Generation.TransferPlan
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! Candidate-reduction transfers are disjoint copies of the existing arithmetic layouts. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.Impl.Dsa.X86.Generation

theorem reduction_input_plan {n : Nat} (upper : n ≤ 48) : TransferPlanFits 40960 (reductionInputTransfers n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    simp only [reductionInputTransfers, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;>
      simp only [TransferFits, VG.Impl.Dsa.Generation.Layout.arithmetic, VG.Impl.Rsa.X86.Keys.slot,
        VG.Impl.Rsa.X86.Keys.hdr, VG.Impl.Rsa.X86.Keys.stride,
        VG.Impl.Mont.X86.Dynamic.slot, VG.Impl.Mont.X86.Dynamic.stride] <;> omega
  · simp [reductionInputTransfers, TransferApart, VG.Impl.Rsa.X86.Keys.slot,
      VG.Impl.Rsa.X86.Keys.hdr, VG.Impl.Rsa.X86.Keys.stride]
    <;> omega
  · intro t ht u hu
    simp only [reductionInputTransfers, List.mem_cons, List.not_mem_nil, or_false] at ht hu
    rcases ht with rfl | rfl <;> rcases hu with rfl | rfl <;>
      simp only [TransferSourceApart, VG.Impl.Dsa.Generation.Layout.arithmetic, VG.Impl.Rsa.X86.Keys.slot,
        VG.Impl.Rsa.X86.Keys.hdr, VG.Impl.Rsa.X86.Keys.stride,
        VG.Impl.Mont.X86.Dynamic.slot, VG.Impl.Mont.X86.Dynamic.stride] <;> omega

theorem reduction_output_plan {n : Nat} (upper : n ≤ 48) : TransferPlanFits 40960 (reductionOutputTransfers n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    simp only [reductionOutputTransfers, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;>
      simp only [TransferFits, VG.Impl.Dsa.Generation.Layout.arithmetic, VG.Impl.Rsa.X86.Keys.slot,
        VG.Impl.Rsa.X86.Keys.hdr, VG.Impl.Rsa.X86.Keys.stride,
        VG.Impl.Mont.X86.Dynamic.slot, VG.Impl.Mont.X86.Dynamic.stride] <;> omega
  · simp [reductionOutputTransfers, TransferApart, VG.Impl.Mont.X86.Dynamic.slot,
      VG.Impl.Mont.X86.Dynamic.stride]
    <;> omega
  · intro t ht u hu
    simp only [reductionOutputTransfers, List.mem_cons, List.not_mem_nil, or_false] at ht hu
    rcases ht with rfl | rfl <;> rcases hu with rfl | rfl <;>
      simp only [TransferSourceApart, VG.Impl.Dsa.Generation.Layout.arithmetic, VG.Impl.Rsa.X86.Keys.slot,
        VG.Impl.Rsa.X86.Keys.hdr, VG.Impl.Rsa.X86.Keys.stride,
        VG.Impl.Mont.X86.Dynamic.slot, VG.Impl.Mont.X86.Dynamic.stride] <;> omega

end VG.Proof.Dsa.X86.Generation
