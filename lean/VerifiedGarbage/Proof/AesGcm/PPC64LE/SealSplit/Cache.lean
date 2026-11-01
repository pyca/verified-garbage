module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealSplit.Entry
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

-- separate module: source arguments survive the shared entry and nonce/AAD stages.
/-! # The split-seal source-argument cache -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.SealSplit
open VG VG.PPC64LE


theorem source_cache {s s₁ s₂ : State} {H : Spec.Gcm.Block} {iv a : List Byte}
    (hs : scratchContract.pre s)
    (h1 : SO1 (stackArg (prepared s) 1) (stackArg (prepared s) 0) (prepared s) s₁)
    (oa : OA s₁.gpr (prepared s).sp H iv a s₁.mem s₂) :
    Spill.Saved (stackArg s 3) s.gpr Impl.AesGcm.PPC64LE.SealSplit.sourceSaved s₂.mem := by
  have hs0 := Prelude.source_saved (allocated 112 s) (prelude_config s hs)
  rw [allocated_work] at hs0
  have hf1 := h1.en.frame
  rw [prepared_work] at hf1
  have hs1 := hs0.frame_in (lo := 112) (n := 16) (by decide) hf1 (by
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide))
  have hf2 := oa.frame
  rw [h1.r30,h1.r31,prepared_work] at hf2
  exact hs1.frame_in (lo := 112) (n := 16) (by decide) hf2 (by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)
    · exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)
    · exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide))


theorem source_layout {s s₁ s₂ : State} {H : Spec.Gcm.Block} {iv a : List Byte}
    (hs : scratchContract.pre s)
    (h1 : SO1 (stackArg (prepared s) 1) (stackArg (prepared s) 0) (prepared s) s₁)
    (oa : OA s₁.gpr (prepared s).sp H iv a s₁.mem s₂)
    (rd : s₂.rd=s₁.rd) (wr : s₂.wr=s₁.wr) :
    Call.Layout s₁.gpr (prepared s).sp (s.gpr .r9) (s.gpr .r10).toNat (sourceState s₂) := by
  have lay := layout_pre s hs
  have cache := source_cache hs h1 oa
  have h27 : s₁.gpr .r27=stackArg s 0 := h1.r27.trans (prepared_destination s hs)
  have h23 : s₁.gpr .r23=stackArg s 1 := h1.r23.trans (prepared_length s hs)
  have h29 : s₁.gpr .r29=s.gpr .r3 := h1.r29.trans (prepared_gpr s .r3 (by decide))
  have h31 : s₁.gpr .r31=stackArg s 3 := h1.r31.trans (prepared_work s)
  have h30 : s₁.gpr .r30=stackArg s 3+16 := by rw [h1.r30,prepared_work]; rfl
  have hslot : Region.Sub ⟨(prepared s).sp+96,8⟩ (stackR s) := Offset.sub_base _ (by decide)
  have hsp : (prepared s).sp.toNat+112≤2^64 := by
    change (s.sp-112#64).toNat+112≤2^64
    rw [toNat_sub_ofNat' lay.spFit.1]
    have := s.sp.isLt
    omega
  have hslotW : InRegions s₂.wr ((prepared s).sp+96) 8 := by
    rw [wr,h1.en.keeps.wr]
    change InRegions (frameR 112 s::s.wr) ((s.sp-112#64)+96) 8
    exact ⟨frameR 112 s,List.mem_cons_self,Offset.contains _ (d := 96) (n := 8) (e := 32) (k := 80) (by decide) (by decide) (by decide)⟩
  refine ⟨?_,?_,?_,?_,lay.fits (sourceR s) (by simp),?_,?_,?_,hslotW,by omega,?_,?_,?_,?_,?_,?_⟩
  · rw [h23]; exact lay.bound
  · change s₂.mem.readW (s₂.gpr .r31+112) 64=s.gpr .r9
    rw [oa.env.r31,h31]
    exact cache (.r9,112) (by decide)
  · change s₂.mem.readW (s₂.gpr .r31+120) 64=BitVec.ofNat 64 (s.gpr .r10).toNat
    rw [oa.env.r31,h31]
    have hh : s₂.mem.readW (stackArg s 3+120) 64=s.gpr .r10 := cache (.r10,120) (by decide)
    rw [hh]
    simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]
  · change Covers [sourceR s] (s₂.rd++s₂.wr)
    rw [rd,wr,h1.en.keeps.rd,h1.en.keeps.wr]
    change Covers [sourceR s] (s.rd++(frameR 112 s::s.wr))
    rw [lay.rd]
    exact Covers.of_mem (by simp)
  · rw [h30]
    exact (lay.workApart (sourceR s) (by simp)).sub_right (Offset.sub_base _ (by decide))
  · rw [h27,h23]; exact lay.dataApart (sourceR s) (by simp)
  · rw [h31]; exact lay.workApart (sourceR s) (by simp)
  · exact SealFused.fit_offset _ hsp (by decide) (off := 96) (n := 8) (by decide)
  · rw [h29]; exact (lay.stackApart (contextR s) (by simp)).sub_left hslot
  · rw [h30]; exact ((lay.stackApart (workR s) (by simp)).sub_left hslot).sub_right (Offset.sub_base _ (by decide))
  · rw [h27,h23]; exact (lay.stackApart (dataR s) (by simp)).sub_left hslot
  · rw [h31]; exact (lay.stackApart (workR s) (by simp)).sub_left hslot
  · exact (lay.stackApart (sourceR s) (by simp)).sub_left hslot

end VG.Proof.AesGcm.PPC64LE.SealSplit
