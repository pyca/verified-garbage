module

public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemVRest
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemReadonlyNoise
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemTransformFrames
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Paired-noise and fused-product encryption composition -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Kem
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
variable {P : KemLay} {L : Layout}
variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

theorem after_noise {s₀ s : State} (hp : Pre P L s₀) (hr : Noise.Room P) (hc : Calls P)
    {kE eo kC co : Nat} (A : EncArgs P L kE eo kC co)
    {mB : Mem} {v : BitVec 64} {rv mv : List Byte} {T : Nat → Poly}
    (hT : ∀j<P.k, decode12 (bytesAt s₀.mem (kA s₀ (L.slot kE)+BitVec.ofNat 64 (eo+384*j)) 384)=T j)
    (htr : Optimized.TransformTables s)
    (h : EInv P L s₀ kC co s.mem mB v rv mv P.k 0 s) (he : Errors P L s₀ rv s)
    (ht : Dot.GammaArtifact s.mem (s.syms "VG_MLKEM_GAMMA"))
    (hcT : Covers [⟨s.syms "VG_MLKEM_GAMMA",512⟩] (s.rd++s.wr))
    (ha : ∀r∈encW P L s₀ kC co, (⟨s.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint r) :
    WP isa (seqs (((List.range P.k).map (Impl.MlKem.AArch64.Optimized.uRow P (slotReg kC) co)) ++
      [Impl.MlKem.AArch64.Optimized.vRest keccak.callee P (slotReg kE) eo .x28 MB (slotReg kC) co])) s
      (fun t => VInv P L s₀ kC co s.mem mB v rv mv P.k P.k t ∧
        bytesAt t.mem (kA s₀ (L.slot kC)+BitVec.ofNat 64 (co+32*P.du*P.k)) (32*P.dv)=
          compressEncode P.dv (vPoly P T rv mv)) := by
  apply WPs.seqs (by simp)
  apply WPs.append
  refine WPs.mono (u_rows hp hr hc A htr h he ht hcT ha) fun t ⟨et,hs⟩ => ?_
  have gt : Dot.GammaArtifact t.mem (t.syms "VG_MLKEM_GAMMA") := by
    rw [hs]; exact gamma_frame ht et.fr ha
  have ct : Covers [⟨t.syms "VG_MLKEM_GAMMA",512⟩] (t.rd++t.wr) := by
    simpa only [hs,et.kb.rd,et.kb.wr,←h.kb.rd,←h.kb.wr] using hcT
  exact WPs.single (v_rest hp hc A hT (transform_enc_frame hp A h.kb et.kb htr hs et.fr) et.vinv gt ct (by simpa only [hs] using ha))

theorem encrypt_rest {s₀ s : State} (hp : Pre P L s₀) (hr : Noise.Room P) (hc : Calls P)
    {kE eo kC co : Nat} (A : EncArgs P L kE eo kC co)
    {mE mB : Mem} {v : BitVec 64} {rv mv : List Byte} {T : Nat → Poly}
    (hT : ∀j<P.k, decode12 (bytesAt s₀.mem (kA s₀ (L.slot kE)+BitVec.ofNat 64 (eo+384*j)) 384)=T j)
    (htr : Optimized.TransformTables s)
    (h : EInv P L s₀ kC co mE mB v rv mv 0 0 s)
    (ht : Dot.GammaArtifact s.mem (s.syms "VG_MLKEM_GAMMA"))
    (hcT : Covers [⟨s.syms "VG_MLKEM_GAMMA",512⟩] (s.rd++s.wr))
    (ha : ∀r∈encW P L s₀ kC co, (⟨s.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint r)
    (hn : ∀r∈Noise.allWrites P false (kA s₀ L.sc), (⟨s.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint r) :
    WP isa (Impl.MlKem.AArch64.Optimized.encryptRest keccak.callee P (slotReg kE) eo .x28 MB (slotReg kC) co) s
      (fun t => ∃mN, Frame (Noise.allWrites P false (kA s₀ L.sc)) s.mem mN ∧
        VInv P L s₀ kC co mN mB v rv mv P.k P.k t ∧
        bytesAt t.mem (kA s₀ (L.slot kC)+BitVec.ofNat 64 (co+32*P.du*P.k)) (32*P.dv)=
          compressEncode P.dv (vPoly P T rv mv)) := by
  refine WP.seq (WP.mono_syms (readonly_noise_einv hp hr htr h) fun t ⟨kt,et,er⟩ hs => ?_)
  have gt : Dot.GammaArtifact t.mem (t.syms "VG_MLKEM_GAMMA") := by
    rw [hs]; exact gamma_frame ht kt.frame hn
  have ct : Covers [⟨t.syms "VG_MLKEM_GAMMA",512⟩] (t.rd++t.wr) := by
    simpa only [hs,kt.rd,kt.wr] using hcT
  have ts := htr.frameFar hs kt.rd kt.wr kt.sp kt.frame
    (Noise.allWrites_tables_far hp.wf hr false
      (by simpa only [R,ptr_zero,hp.scl] using
        cov_w hp h.kb ⟨hp.scw,hp.scb⟩ (o:=0) (l:=P.scl) (by rw [hp.scl]; omega)) htr)
  exact WP.mono (after_noise hp hr hc A hT ts et er gt ct (by simpa only [hs] using ha))
    fun u ⟨eu,vu⟩ => ⟨t.mem,kt.frame,eu,vu⟩

end VG.Proof.MlKem.AArch64.Kem
