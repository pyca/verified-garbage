module

import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.URow
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemUContext
import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.Ops
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemTransformFrames
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.DotSpec
import VerifiedGarbage.Proof.Framework.AArch64.Syms
public import VerifiedGarbage.Impl.MlKem.AArch64.Kem16
public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Table
public import VerifiedGarbage.Proof.MlKem.AArch64.DotW.Loop
public import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.Noise
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemURow

/-! # The rows of `u`, keeping `e₂`

`u_rowsE`: `Kem16.u_rowsW`, with a polynomial at `EP` (`e₂`, which the
matrix computed) kept through the rows. -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Kem
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Impl.MlKem.AArch64.Noise (noiseOff)
variable {P : KemLay} {L : Layout}

theorem fused_u_rowE {s₀ s : State} (hp : Pre P L s₀) (hr : Noise.Room P) (hc : Calls P)
    {kE eo kC co : Nat} (A : EncArgs P L kE eo kC co)
    {mE mB : Mem} {v : BitVec 64} {rv mv : List Byte} {i : Nat} (hi : i<P.k)
    (h : EInvW true P L s₀ kC co mE mB v rv mv P.k i s)
    {F G : (Nat × Nat) → Poly}
    (hd : DotW.LoopDataW s .x28 .x28 (s.gpr .x28+BitVec.ofNat 64 (TP P)) (s.syms "VG_MLKEM_GAMMA")
      (uTerms P i) (Dot.polyValues F) (Dot.polyValues G) Dot.gammaValues)
    (hsum : Dot.polySum (uTerms P i) F G = KPke.dotK (fun j => aMW true P L s₀ mB j i) (encY rv) P.k)
    (ht : Optimized.TransformTables s)
    (he : PolyIsW 16 s.mem (sA L s₀ (noiseOff P i)) (cbd rv (P.k+i)))
    {E : Poly} (hE : PolyIsW 16 s.mem (sA L s₀ (EP P)) E) :
    WP isa (Kem16.uRow P (slotReg kC) co i) s
      (fun t => EInvW true P L s₀ kC co mE mB v rv mv P.k (i+1) t ∧ PolyIsW 16 t.mem (sA L s₀ (EP P)) E) := by
  have hw := hp.wf
  have hn : i≤P.k := Nat.le_of_lt hi
  have ef : noiseOff P i+1024≤L.len L.sc := by rw [hp.scl]; exact Noise.noise_fits hr hi
  have ep := Noise.noise_past_kem hr i
  have far : ∀r∈[R (kA s₀) L.sc (TP P) 1024,R (kA s₀) L.sc NS 1024],
      (polyRegion (sA L s₀ (noiseOff P i))).Disjoint r := by
    intro r hh
    rcases mem2' hh with rfl | rfl <;>
      exact hp.args.rdisj hp.scb hp.scb ef (hp.fs (by lom)) (.inl rfl) (.inr (.inr (by lom)))
  simp only [Kem16.uRow, seqs]
  refine WP.seq (WP.mono_syms (WP.mono (fusedW_ok hp (po_TP hw) h.kb (uTerms P i) hd)
    fun t ⟨kt,ft,pt,xt⟩ => (⟨h.frame hp kt xt ft (far_one hp A (Nat.le_refl _) hn (by lom) (by lom)),ft,pt⟩ :
      EInvW true P L s₀ kC co mE mB v rv mv P.k i t ∧ _ ∧ _)) fun s₁ ⟨e₁,f₁,t₁⟩ sy₁ => ?_)
  have p₁ : PolyIsW 16 s₁.mem _ _ := polyIsW_frame_poly (w16 := true) f₁
    (fun r hh => far r (by rw [List.mem_singleton.mp hh]; exact List.mem_cons_self ..)) he
  rw [hsum] at t₁
  have q₁ : PolyIsW 16 s₁.mem _ _ := polyIsW_frame_poly (w16 := true) f₁ (fun r hh => by
    rw [List.mem_singleton.mp hh]; exact papart hp (po_EP hw) (po_TP hw) (by lom)) hE
  have ht₁ := ht.frame sy₁ (e₁.kb.rd.trans h.kb.rd.symm) (e₁.kb.wr.trans h.kb.wr.symm) (e₁.kb.sp.trans h.kb.sp.symm)
    f₁ (cov_w hp h.kb ⟨hp.scw,hp.scb⟩ (o:=TP P) (l:=1024) (hp.fs (by lom)))
  refine WP.seq (WP.mono (invW_ok hp (po_TP hw) e₁.kb t₁.1 ht₁) fun s₂ ⟨kb₂,f₂,t₂,x₂⟩ => ?_)
  have e₂ := e₁.frame hp kb₂ x₂ f₂ (far_mul hp A (Nat.le_refl _) hn (by lom) (by lom))
  have p₂ : PolyIsW 16 s₂.mem _ _ := polyIsW_frame_poly (w16 := true) f₂ far p₁
  rw [t₁.2] at t₂
  have q₂ : PolyIsW 16 s₂.mem _ _ := polyIsW_frame_poly (w16 := true) f₂ (fun r hh => by
    rcases mem2' hh with rfl | rfl
    · exact papart hp (po_EP hw) (po_TP hw) (by lom)
    · exact sdisj hp (po_EP hw).le (by lom) (by lom)) q₁
  refine WP.seq (WP.mono (addW_read_ok hp (po_TP hw) (Noise.noise_fits hr hi)
    (.inl (by lom)) e₂.kb t₂.1 p₂.1) fun s₃ ⟨kb₃,f₃,t₃,x₃⟩ => ?_)
  have e₃ := e₂.frame hp kb₃ x₃ f₃ (far_one hp A (Nat.le_refl _) hn (by lom) (by lom))
  rw [t₂.2,p₂.2] at t₃
  have q₃ : PolyIsW 16 s₃.mem _ _ := polyIsW_frame_poly (w16 := true) f₃ (fun r hh => by
    rw [List.mem_singleton.mp hh]; exact papart hp (po_EP hw) (po_TP hw) (by lom)) q₂
  refine WP.seq (WP.mono (widenW_ok hp (po_TP hw) (po_PP hw) (.inl (by lom)) e₃.kb t₃)
    fun s₄ ⟨kb₄,f₄,t₄,x₄⟩ => ?_)
  have e₄ := e₃.frame hp kb₄ x₄ f₄ (far_one hp A (Nat.le_refl _) hn (by lom) (by lom))
  have q₄ : PolyIsW 16 s₄.mem _ _ := polyIsW_frame_poly (w16 := true) f₄ (fun r hh => by
    rw [List.mem_singleton.mp hh]; exact papart hp (po_EP hw) (po_PP hw) (by lom)) q₃
  have fC := A.fC
  have hu := du_le hi
  refine WP.mono (ceL_ok hp hc (off := PP P) (d := P.du) (k := kC) (o := co+32*P.du*i)
    (po_PP hw) (.inl rfl) A.hkC A.wC (by lom) (by
      rcases A.sC with hC | hC
      · exact .inl hC
      · exact .inr ⟨by subst hC; lom,.inr (by subst hC; lom)⟩)
    e₄.kb t₄.1) fun s₅ ⟨kb₅,f₅,b₅,x₅⟩ => ?_
  have e₅ := e₄.frame hp kb₅ x₅ f₅ fun r hh => by
    rw [List.mem_singleton.mp hh]; exact far_ct hp A (Nat.le_refl _) (by lom)
  have q₅ : PolyIsW 16 s₅.mem _ _ := polyIsW_frame_poly (w16 := true) f₅ (fun r hh => by
    rw [List.mem_singleton.mp hh]
    refine hp.args.rdisj hp.scb (hp.lt A.hkC) (hp.fs (po_EP hw).le) (by lom) (.inr (.inr A.wC)) ?_
    rcases A.sC with hC | hC
    · exact .inl (Ne.symm hC)
    · subst hC; exact .inr (.inl (by lom))) q₄
  refine ⟨⟨e₅.kb,e₅.x24,e₅.r,e₅.m,e₅.a,e₅.y,fun j hj => ?_,e₅.fr⟩, q₅⟩
  rcases (by omega : j<i ∨ j=i) with hj | rfl
  · exact e₅.u j hj
  · rw [b₅,t₄.2]; rfl

theorem u_rowsE {s₀ s : State} (hp : Pre P L s₀) (hr : Noise.Room P) (hc : Calls P)
    {kE eo kC co : Nat} (A : EncArgs P L kE eo kC co)
    {mB : Mem} {v : BitVec 64} {rv mv : List Byte}
    (htr : Optimized.TransformTables s)
    (h : EInvW true P L s₀ kC co s.mem mB v rv mv P.k 0 s) (he : ErrorsW P L s₀ rv s)
    (ht : Dot.GammaArtifact s.mem (s.syms "VG_MLKEM_GAMMA"))
    (hcT : Covers [⟨s.syms "VG_MLKEM_GAMMA",512⟩] (s.rd++s.wr))
    (ha : ∀r∈encW P L s₀ kC co, (⟨s.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint r)
    {E : Poly} (hE : PolyIsW 16 s.mem (sA L s₀ (EP P)) E) :
    WPs ((List.range P.k).map (Kem16.uRow P (slotReg kC) co)) s
      (fun t => EInvW true P L s₀ kC co s.mem mB v rv mv P.k P.k t ∧ t.syms=s.syms ∧
        PolyIsW 16 t.mem (sA L s₀ (EP P)) E) := by
  apply WPs.range (I := fun i t => EInvW true P L s₀ kC co s.mem mB v rv mv P.k i t ∧ t.syms=s.syms ∧
    PolyIsW 16 t.mem (sA L s₀ (EP P)) E)
  · intro i hi t ⟨ei,hs,qi⟩
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
    exact WP.mono_syms (fused_u_rowE hp hr hc A hi ei (u_readyW hp hi ei gt ct da).data
      (u_sumW hi ei) (transform_enc_frame hp A h.kb ei.kb htr hs ei.fr) (et i hi) qi)
      fun u ⟨hu,qu⟩ hsu => ⟨hu,hsu.trans hs,qu⟩
  · exact ⟨h,rfl,hE⟩

end VG.Proof.MlKem.AArch64.Kem
