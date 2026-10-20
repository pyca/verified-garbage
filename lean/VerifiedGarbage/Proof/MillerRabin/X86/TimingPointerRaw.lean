module

import VerifiedGarbage.Proof.MillerRabin.X86.TimingBase
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingBlocks

/-! # Array addressing executes only fixed public-register operations -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Dsa.X86

theorem scaleIndex_raw (r : Reg) (j : Nat) (dst : r ∈ [.ebp, .ebx, .ecx]) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (.block (scaleIndex r .edx j))
      (VG.X86.Taint.Agree (roundTaint [.edi])) := by
  apply blockFlatMap_relCT
  intro bit
  apply RelCT.block_append
  apply RelCT.seq
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at dst
    rcases dst with rfl | rfl | rfl <;> exact checkedBlockInvariant rfl rfl
  · split
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at dst
      rcases dst with rfl | rfl | rfl <;> exact checkedBlockInvariant rfl rfl
    · exact RelCT.block_nil (fun _ _ H => H)

theorem ptr_raw (r : Reg) (j : Nat) (dst : r ∈ [.ebp, .ebx, .ecx]) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (.block (ptr r j))
      (VG.X86.Taint.Agree (roundTaint [.edi])) := by
  unfold ptr
  split
  · refine erased_relCT (.block [.mov r (.mem (slot (64 + 8 * j)))])
      (.block [.mov r (.mem (slot 0))]) (.block []) rfl rfl rfl ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at dst
    rcases dst with rfl | rfl | rfl <;> rfl
  · rw [List.append_assoc]
    apply RelCT.block_append
    refine RelCT.seq (R := VG.X86.Taint.Agree (roundTaint [.edi])) ?_ ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at dst
      rcases dst with rfl | rfl | rfl <;> exact checkedBlockInvariant rfl rfl
    · apply RelCT.block_append
      apply RelCT.seq (scaleIndex_raw r j dst)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at dst
      rcases dst with rfl | rfl | rfl <;> exact checkedBlockInvariant rfl rfl

theorem words_raw : RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (.block words)
    (VG.X86.Taint.Agree (roundTaint [.edi])) := checkedBlockInvariant rfl rfl

end VG.Proof.MillerRabin.X86
