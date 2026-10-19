module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.EntryLink
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.EntryBody
import VerifiedGarbage.Proof.Framework.Omega

/-! Every generation phase leaves the saved link word untouched. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

theorem link_separate {s : State} (h : GenerationABI s) :
    ∀ r ∈ (contextOf h).changed ++ [⟨s.gpr .x0, (s.gpr .x1).toNat⟩], (linkRegion s).Disjoint r := by
  intro r hr
  change r ∈ [⟨stackArg s 2, usedBytes (s.gpr .x2).toNat⟩,
    ⟨generationBase s, frameBytes⟩, below (generationBase s) 16, ⟨s.gpr .x0, (s.gpr .x1).toNat⟩] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (h.stackScratch.sub_left (link_sub s)).sub_right (generation_scratch_sub h)
  · exact (Offset.base_disjoint (generationBase s) (e := 296) (n := 152) (k := frameBytes) (by decide) (by decide)).symm
  · exact Offset.disjoint_below (generationBase s) (n := 16) (d := 296) (k := 152) (by decide)
  · exact h.stackOut.sub_left (link_sub s)

theorem link_saved {s t : State} (h : GenerationABI s)
    (hf : Frame ((contextOf h).changed ++ [⟨s.gpr .x0, (s.gpr .x1).toNat⟩]) (linkState s).mem t.mem) :
    VG.Proof.Bignum.word t.mem (generationBase s) 296 = s.gpr .x30 := by
  have hc : (linkRegion s).Contains (off (generationBase s) 296) 8 := by
    have hc := Offset.contains_base (off (generationBase s) 296) (d := 0) (n := 8) (k := 152)
      (by decide) (by decide)
    simpa only [linkRegion, off, BitVec.add_zero] using hc
  have hm : VG.Proof.Bignum.word t.mem (generationBase s) 296 =
      VG.Proof.Bignum.word (linkState s).mem (generationBase s) 296 :=
    hf.readW (w := 64) hc (link_separate h) (by decide : 64 / 8 < 2 ^ 64)
  have hl : VG.Proof.Bignum.word (linkState s).mem (generationBase s) 296 = s.gpr .x30 :=
    word_writeW_self (savedAbiMem s) (generationBase s) 296 (s.gpr .x30)
  exact hm.trans hl

end VG.Proof.Dsa.AArch64.Generation
