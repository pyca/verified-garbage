import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.OutCore
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TableArtifact

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

theorem staticInit_ok (s : State) :
    WP isa (.block [.adrSym .x1 "VG_MLDSA_NTT_EXPANDED"]) s fun t =>
      (t.gpr .x1=s.syms "VG_MLDSA_NTT_EXPANDED" ∧ t.mem=s.mem) ∧ Keep [.x1] s t := by
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  arun [exec_adrSym]

theorem outInit_ok (s : State) :
    WP isa (.block [.addImm .x .x11 .x1 0,.adrSym .x1 "VG_MLDSA_NTT_EXPANDED"]) s fun t =>
      (t.gpr .x1=s.syms "VG_MLDSA_NTT_EXPANDED" ∧ t.gpr .x11=s.gpr .x1 ∧ t.mem=s.mem) ∧
      Keep [.x1,.x11] s t := by
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  arun [exec_adrSym]
  rfl

theorem staticNtt_words_ok {s : State}
    (ht : ExpandedArtifact s.mem (s.syms "VG_MLDSA_NTT_EXPANDED"))
    (htr : expandedRegion (s.syms "VG_MLDSA_NTT_EXPANDED") ∈ s.rd++s.wr)
    (hw : outputRegion (s.gpr .x0) ∈ s.wr)
    (hsep : (expandedRegion (s.syms "VG_MLDSA_NTT_EXPANDED")).Disjoint (outputRegion (s.gpr .x0))) :
    WP isa staticNtt s fun t => Keep (.x1::nttGprs) s t ∧ Frame [outputRegion (s.gpr .x0)] s.mem t.mem ∧
      t.mem=nttMemory s.mem (s.gpr .x0) ordinaryRoot innerRoot tailRoot := by
  unfold staticNtt
  refine WP.seq (WP.mono (staticInit_ok s) fun s₁ ⟨⟨ha,hm⟩,hk⟩ => ?_)
  have hr : ExpandedArtifact s₁.mem (s₁.gpr .x1) := by simpa only [hm,ha] using ht
  refine WP.mono (renamedNtt_words_ok hr.roots.1 hr.roots.2 ?_ ?_ ?_) fun t ⟨hk₁,hf₁,hm₁⟩ => ?_
  · simpa only [ha,hk.rd,hk.wr] using htr
  · simpa only [hk.get .x0,hk.wr] using hw
  · simpa only [ha,hk.get .x0] using hsep
  · exact ⟨(hk.trans hk₁).mono,by simpa only [hm,hk.get .x0] using hf₁,
      by simpa only [hm,hk.get .x0] using hm₁⟩

theorem outNtt_words_ok {s : State}
    (ht : ExpandedArtifact s.mem (s.syms "VG_MLDSA_NTT_EXPANDED"))
    (htr : expandedRegion (s.syms "VG_MLDSA_NTT_EXPANDED") ∈ s.rd++s.wr)
    (hr : outputRegion (s.gpr .x1) ∈ s.rd++s.wr)
    (hw : outputRegion (s.gpr .x0) ∈ s.wr)
    (hsep : (expandedRegion (s.syms "VG_MLDSA_NTT_EXPANDED")).Disjoint (outputRegion (s.gpr .x0))) :
    WP isa outNtt s fun t => Keep (.x1::outGprs) s t ∧ Frame [outputRegion (s.gpr .x0)] s.mem t.mem ∧
      t.mem=outMemory s.mem (s.gpr .x0) (s.gpr .x1) ordinaryRoot innerRoot tailRoot := by
  unfold outNtt
  refine WP.seq (WP.mono (outInit_ok s) fun s₁ ⟨⟨ha,hs,hm⟩,hk⟩ => ?_)
  have hrt : ExpandedArtifact s₁.mem (s₁.gpr .x1) := by simpa only [hm,ha] using ht
  refine WP.mono (outBody_words_ok hrt.roots.1 hrt.roots.2 ?_ ?_ ?_ ?_) fun t ⟨hk₁,hf₁,hm₁⟩ => ?_
  · simpa only [ha,hk.rd,hk.wr] using htr
  · simpa only [hs,hk.rd,hk.wr] using hr
  · simpa only [hk.get .x0,hk.wr] using hw
  · simpa only [ha,hk.get .x0] using hsep
  · exact ⟨(hk.trans hk₁).mono,by simpa only [hm,hk.get .x0] using hf₁,
      by simpa only [hm,hk.get .x0,hs] using hm₁⟩

end VG.Proof.MlDsa.AArch64.Optimized
