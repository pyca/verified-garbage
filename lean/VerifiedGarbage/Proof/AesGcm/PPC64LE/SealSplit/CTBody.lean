module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealSplit.Body
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealSplit.CTPartial
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealSplit.Body
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealSplit.CTPartial

-- separate module: restore public source arguments before the shared constant-time text stages.
/-! # Constant time of the split-seal body -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.SealSplit.CTBlocks
open VG VG.PPC64LE


theorem body_ct [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    {c W sp : Addr} {R count : Nat} {Np : Addr} {n : Nat} {Ad A D N S : BitVec 64}
    (L : Lay c (W+BitVec.ofNat 64 16) W) (hv : R=10 ∨ R=12 ∨ R=14)
    (I : State → Prop) (hone : ∀ s, I s → OneI c W sp R Np n Ad A D N s)
    (hsi : ∀ s, I s → SI c (W+BitVec.ofNat 64 16) W sp R A D N S count (sourceState s)) :
    CT I Impl.AesGcm.PPC64LE.SealSplit.body := by
  have hbi : ∀ s, I s → SealFusedCT.BI c (W+BitVec.ofNat 64 16) W sp R A D N s :=
    fun s hs => SealFusedCT.one_bi (hone s hs)
  refine CT.ite (N == 0) (fun s hs => ?_)
    (fun _ => (SealFusedCT.smallBody_ct L hv).mono hone) (fun _ => ?_)
  · obtain ⟨V,_,_,_,_,_,_,hn,he,_⟩ := hbi s hs
    simp only [eval,State.read,Size.bits,BitVec.setWidth_eq,he.fr .r23 (by decide),hn]
  · refine CT.seq (J := SI c (W+BitVec.ofNat 64 16) W sp R A D N S count) ?_ ?_ (partial_finish_ct L hv)
    · exact CT.taint [.r31] (fun s t hs ht =>
        ⟨(SealFusedCT.bi_agree (hbi s hs) (hbi t ht)).1,fun r hr =>
          (SealFusedCT.bi_agree (hbi s hs) (hbi t ht)).2 r (by
            simp only [List.mem_singleton] at hr
            subst r
            decide)⟩) (by taint_decide)
    · intro s hs
      obtain ⟨_,_,_,_,_,_,_,_,he,_⟩ := hbi s hs
      exact WP.mono (source_ok he) fun t ht => ht ▸ hsi s hs

end VG.Proof.AesGcm.PPC64LE.SealSplit.CTBlocks
