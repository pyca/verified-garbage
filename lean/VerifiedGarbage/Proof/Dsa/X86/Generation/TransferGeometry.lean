module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.TransferPlan
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! The exponent save and compact preparation are disjoint transfer plans. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.Impl.Dsa.X86.Generation

theorem save_exponent_plan {n : Nat} (hn : n ≤ 48) :
    TransferPlanFits 40960 (saveExponentTransfers n) := by
  refine ⟨fun _ ht => save_exponent_transfers_fit hn ht, ?_, ?_⟩
  · simp [saveExponentTransfers, TransferApart]
    <;> omega
  · intro t ht u hu
    simp only [saveExponentTransfers, List.mem_cons, List.not_mem_nil, or_false] at ht hu
    rcases ht with rfl | rfl <;> rcases hu with rfl | rfl <;>
      simp only [TransferSourceApart, VG.Impl.Mont.X86.Dynamic.slot, VG.Impl.Mont.X86.Dynamic.stride,
        VG.Impl.Dsa.Generation.Layout.arithmetic] <;> omega

theorem compact_plan {n : Nat} (hn : n ≤ 48) : TransferPlanFits 40960 (compactTransfers n) := by
  refine ⟨fun _ ht => compact_transfers_fit hn ht, ?_, ?_⟩
  · simp [compactTransfers, compactNumberTransfer, TransferApart,
      VG.Spec.Rsa.Mont.arrAt, VG.Spec.Rsa.Mont.hdrBytes]
    <;> omega
  · intro t ht u hu
    simp only [compactTransfers, List.mem_cons, List.not_mem_nil, or_false] at ht hu
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [TransferSourceApart, compactNumberTransfer, VG.Impl.Mont.X86.Dynamic.slot,
        VG.Impl.Mont.X86.Dynamic.stride, VG.Impl.Dsa.Generation.Layout.arithmetic,
        VG.Spec.Rsa.Mont.arrAt, VG.Spec.Rsa.Mont.hdrBytes] <;> omega

end VG.Proof.Dsa.X86.Generation
