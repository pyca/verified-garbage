module

public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemUContext
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemReadonlyURow
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemTransformFrames
public import VerifiedGarbage.Impl.MlKem.AArch64.Optimized
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # All fused ciphertext rows from the precomputed noise -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Kem
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
variable {P : KemLay} {L : Layout}

theorem u_rows {s₀ s : State} (hp : Pre P L s₀) (hr : Noise.Room P) (hc : Calls P)
    {kE eo kC co : Nat} (A : EncArgs P L kE eo kC co)
    {mB : Mem} {v : BitVec 64} {rv mv : List Byte}
    (htr : Optimized.TransformTables s)
    (h : EInv P L s₀ kC co s.mem mB v rv mv P.k 0 s) (he : Errors P L s₀ rv s)
    (ht : Dot.GammaArtifact s.mem (s.syms "VG_MLKEM_GAMMA"))
    (hcT : Covers [⟨s.syms "VG_MLKEM_GAMMA",512⟩] (s.rd++s.wr))
    (ha : ∀r∈encW P L s₀ kC co, (⟨s.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint r) :
    WPs ((List.range P.k).map (Impl.MlKem.AArch64.Optimized.uRow P (slotReg kC) co)) s
      (fun t => EInv P L s₀ kC co s.mem mB v rv mv P.k P.k t ∧ t.syms=s.syms) := by
  apply WPs.range (I := fun i t => EInv P L s₀ kC co s.mem mB v rv mv P.k i t ∧ t.syms=s.syms)
  · intro i hi t ⟨ei,hs⟩
    have et := he.frame_enc hp hr A ei.fr
    have gt : Dot.GammaArtifact t.mem (t.syms "VG_MLKEM_GAMMA") := by
      rw [hs]; exact gamma_frame ht ei.fr ha
    have ct : Covers [⟨t.syms "VG_MLKEM_GAMMA",512⟩] (t.rd++t.wr) := by
      simpa only [hs,ei.kb.rd,ei.kb.wr,←h.kb.rd,←h.kb.wr] using hcT
    have da : (polyRegion (sA L s₀ (TP P))).Disjoint ⟨t.syms "VG_MLKEM_GAMMA",512⟩ := by
      rw [hs]
      have hw := hp.wf
      have hsub : Region.Sub (R (kA s₀) L.sc (TP P) 1024) (R (kA s₀) L.sc PB (SV P-PB)) :=
        R.sub2 (by lom) (by lom)
      exact ((ha _ (by simp [encW])).sub_right hsub).symm
    exact WP.mono_syms (readonly_fused_u_row hp hr hc A hi ei (u_ready hp hi ei gt ct da).data
      (u_sum hi ei) (transform_enc_frame hp A h.kb ei.kb htr hs ei.fr) (et i hi)) fun u hu hsu => ⟨hu,hsu.trans hs⟩
  · exact ⟨h,rfl⟩

end VG.Proof.MlKem.AArch64.Kem
