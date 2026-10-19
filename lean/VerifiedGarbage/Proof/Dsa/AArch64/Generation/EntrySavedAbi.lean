module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.EntrySavedLink

/-! The generation phases preserve the saved AAPCS64 registers. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64.Generation

theorem link_gprs (s : State) : Spill.Saved (generationBase s) s.gpr abiGprs (linkState s).mem := by
  have g := Spill.saveMem_saved (l := abiGprs) (by decide) s.mem (generationBase s) s.gpr
  have vf := Spill.saveMem_frame (l := vectorSlots) (lo := 384) (n := 64) (by decide) (by decide)
    (Spill.saveMem s.mem (generationBase s) s.gpr abiGprs) (generationBase s) (vectorValues s)
  have gv := g.frame_in (lo := 304) (n := 80) (by decide) vf (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact Offset.disjoint (generationBase s) (by decide) (by decide) (by decide))
  have lf : Frame [⟨off (generationBase s) 296, 8⟩] (savedAbiMem s) (linkState s).mem :=
    by
      change Frame [⟨off (generationBase s) 296, 8⟩] (savedAbiMem s)
        ((savedAbiMem s).writeW (off (generationBase s) 296) (s.gpr .x30))
      exact (Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)
  exact gv.frame_in (lo := 304) (n := 80) (by decide) lf (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact Offset.disjoint (generationBase s) (by decide) (by decide) (by decide))

theorem link_vectors (s : State) :
    Spill.Saved (generationBase s) (vectorValues s) vectorSlots (linkState s).mem := by
  have v := Spill.saveMem_saved (l := vectorSlots) (by decide)
    (Spill.saveMem s.mem (generationBase s) s.gpr abiGprs) (generationBase s) (vectorValues s)
  have lf : Frame [⟨off (generationBase s) 296, 8⟩] (savedAbiMem s) (linkState s).mem :=
    by
      change Frame [⟨off (generationBase s) 296, 8⟩] (savedAbiMem s)
        ((savedAbiMem s).writeW (off (generationBase s) 296) (s.gpr .x30))
      exact (Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)
  exact v.frame_in (lo := 384) (n := 64) (by decide) lf (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact Offset.disjoint (generationBase s) (by decide) (by decide) (by decide))

theorem entryAbi_saved {s t : State} (h : GenerationABI s)
    (hf : Frame ((contextOf h).changed ++ [⟨s.gpr .x0, (s.gpr .x1).toNat⟩]) (linkState s).mem t.mem) :
    Spill.Saved (generationBase s) s.gpr abiGprs t.mem ∧
    Spill.Saved (generationBase s) (vectorValues s) vectorSlots t.mem := by
  exact ⟨(link_gprs s).frame_in (lo := 296) (n := 152) (by decide) hf (link_separate h),
    (link_vectors s).frame_in (lo := 296) (n := 152) (by decide) hf (link_separate h)⟩

end VG.Proof.Dsa.AArch64.Generation
