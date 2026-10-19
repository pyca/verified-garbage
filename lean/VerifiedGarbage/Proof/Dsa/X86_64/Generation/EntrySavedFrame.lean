module
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ABIContext
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntryAllocated
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntrySave

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-! # Search workspaces cannot overwrite the saved calling-convention registers -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.X86_64.Spill VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

theorem savedBase_eq (s : State) : savedBase s = off (generationBase s) 296 := by
  simp only [savedBase, generationBase, off]
  bv_omega

theorem saved_disjoint {s : State} (h : GenerationABI s) :
    ∀ r ∈ (contextOf h).changed ++ [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩],
      (⟨savedBase s, 48⟩ : Region).Disjoint r := by
  intro r hr
  simp only [GenerationContext.changed, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl | rfl) | rfl
  · exact (h.stackScratch.sub_left (saved_frame_sub s)).sub_right (generation_scratch_sub h)
  · change (⟨savedBase s, 48⟩ : Region).Disjoint ⟨generationBase s, frameBytes⟩
    rw [savedBase_eq]
    exact Offset.disjoint_base _ (by decide) (by decide)
  · change (⟨savedBase s, 48⟩ : Region).Disjoint (below (generationBase s) 128)
    rw [savedBase_eq]
    exact Offset.disjoint_below _ (by decide)
  · exact h.stackOut.sub_left (saved_frame_sub s)

theorem saved_across_generator {s u t : State} (h : GenerationABI s)
    (saved : Saved u.mem (savedBase s) s.gpr spillSlots)
    (hf : Frame ((contextOf h).changed ++ [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩]) u.mem t.mem) :
    Saved t.mem (savedBase s) s.gpr spillSlots := by
  apply saved.frame hf
  intro p hp r hr
  exact (saved_disjoint h r hr).sub_left (Offset.sub_base _ (spillSlots_fit p hp))

end VG.Proof.Dsa.X86_64.Generation
