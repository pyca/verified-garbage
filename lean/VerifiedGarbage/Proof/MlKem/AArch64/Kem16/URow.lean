module

public import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.Noise
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemURows
import VerifiedGarbage.Proof.Framework.AArch64.Syms

/-! # The 16-bit ciphertext rows

`u_rowsW`: the rows of `u` of `Kem16.encryptRest`, from `Â` and `ŷ` stored with
16 bits (`EInvW true`) and the errors `e₁` (`ErrorsW`): each row is the fused
dot product, the inverse transform and the sum in 16 bits, widened into `PP`
for the compression. -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Kem
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Impl.MlKem.AArch64.Noise (noiseOff)
variable {P : KemLay} {L : Layout}

theorem fused_readyW {s₀ s : State} (hp : Pre P L s₀) (hk : KB P L s₀ s)
    {off : Nat} (ho : PO P off) {terms : List (Nat × Nat)} {F G : (Nat × Nat) → Poly}
    (hn : terms.length≤4)
    (hf : ∀ fg∈terms, PO P fg.1) (hg : ∀ fg∈terms, PO P fg.2)
    (hF : ∀ fg∈terms, PolyIsW 16 s.mem (sA L s₀ fg.1) (F fg))
    (hG : ∀ fg∈terms, PolyIsW 16 s.mem (sA L s₀ fg.2) (G fg))
    (df : ∀ fg∈terms, off+1024≤fg.1 ∨ fg.1+1024≤off)
    (dg : ∀ fg∈terms, off+1024≤fg.2 ∨ fg.2+1024≤off)
    (ht : Dot.GammaArtifact s.mem (s.syms "VG_MLKEM_GAMMA"))
    (hc : Covers [⟨s.syms "VG_MLKEM_GAMMA",512⟩] (s.rd++s.wr))
    (ha : (polyRegion (sA L s₀ off)).Disjoint ⟨s.syms "VG_MLKEM_GAMMA",512⟩) :
    DotW.ReadyW s (s.gpr .x28+BitVec.ofNat 64 off) (s.syms "VG_MLKEM_GAMMA") terms F G := by
  refine ⟨hn,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,hc,ht⟩
  · intro fg hh; have := (hf fg hh).le; kom
  · intro fg hh; have := (hg fg hh).le; kom
  · intro fg hh; rw [e28 hk]; exact hF fg hh
  · intro fg hh; rw [e28 hk]; exact hG fg hh
  · intro fg hh; rw [e28 hk,e28 hk]; exact papart hp ho (hf fg hh) (df fg hh)
  · intro fg hh; rw [e28 hk,e28 hk]; exact papart hp ho (hg fg hh) (dg fg hh)
  · intro fg hh; rw [e28 hk]; exact cov_sr hp hk (hf fg hh).le
  · intro fg hh; rw [e28 hk]; exact cov_sr hp hk (hg fg hh).le
  · rw [e28 hk]; exact cov_s hp hk ho.le
  · rwa [e28 hk]

def uFW (L : Layout) (s₀ s : State) (fg : Nat × Nat) : Poly := polyAtW 16 s.mem (sA L s₀ fg.1)
def uGW (L : Layout) (s₀ s : State) (fg : Nat × Nat) : Poly := polyAtW 16 s.mem (sA L s₀ fg.2)

theorem u_sumW {s₀ s : State} {kC co : Nat} {mE mB : Mem} {v : BitVec 64}
    {rv mv : List Byte} {i : Nat} (hi : i<P.k)
    (h : EInvW true P L s₀ kC co mE mB v rv mv P.k i s) :
    Dot.polySum (uTerms P i) (uFW L s₀ s) (uGW L s₀ s)=
      KPke.dotK (fun j => aMW true P L s₀ mB j i) (encY rv) P.k := by
  apply Optimized.polySum_dotK
  · intro j hj; exact (h.a j hj i hi).2
  · intro j hj; exact (h.y j hj).2

theorem u_readyW {s₀ s : State} (hp : Pre P L s₀)
    {kC co : Nat} {mE mB : Mem} {v : BitVec 64} {rv mv : List Byte} {i : Nat} (hi : i<P.k)
    (h : EInvW true P L s₀ kC co mE mB v rv mv P.k i s)
    (ht : Dot.GammaArtifact s.mem (s.syms "VG_MLKEM_GAMMA"))
    (hc : Covers [⟨s.syms "VG_MLKEM_GAMMA",512⟩] (s.rd++s.wr))
    (ha : (polyRegion (sA L s₀ (TP P))).Disjoint ⟨s.syms "VG_MLKEM_GAMMA",512⟩) :
    DotW.ReadyW s (s.gpr .x28+BitVec.ofNat 64 (TP P)) (s.syms "VG_MLKEM_GAMMA")
      (uTerms P i) (uFW L s₀ s) (uGW L s₀ s) := by
  have hw := hp.wf
  have term : ∀fg∈uTerms P i, ∃j<P.k, fg=(aOff P j i,yOff P j) := by
    intro fg hh
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hh
    exact ⟨j,List.mem_range.mp hj,rfl⟩
  refine fused_readyW hp h.kb (po_TP hw) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ht hc ha
  · simpa only [uTerms,List.length_map,List.length_range] using hw.facts.2.1
  · intro fg hh; obtain ⟨j,hj,rfl⟩ := term fg hh; exact po_a hw hj hi
  · intro fg hh; obtain ⟨j,hj,rfl⟩ := term fg hh; exact po_y hw hj
  · intro fg hh; obtain ⟨j,hj,rfl⟩ := term fg hh; exact ⟨(h.a j hj i hi).1,rfl⟩
  · intro fg hh; obtain ⟨j,hj,rfl⟩ := term fg hh; exact ⟨(h.y j hj).1,rfl⟩
  · intro fg hh; obtain ⟨j,hj,rfl⟩ := term fg hh
    have := ij_lt hj hi
    exact .inr (by lom)
  · intro fg hh; obtain ⟨j,hj,rfl⟩ := term fg hh
    exact .inr (by lom)

theorem fused_u_rowW {s₀ s : State} (hp : Pre P L s₀) (hr : Noise.Room P) (hc : Calls P)
    {kE eo kC co : Nat} (A : EncArgs P L kE eo kC co)
    {mE mB : Mem} {v : BitVec 64} {rv mv : List Byte} {i : Nat} (hi : i<P.k)
    (h : EInvW true P L s₀ kC co mE mB v rv mv P.k i s)
    {F G : (Nat × Nat) → Poly}
    (hd : DotW.LoopDataW s .x28 .x28 (s.gpr .x28+BitVec.ofNat 64 (TP P)) (s.syms "VG_MLKEM_GAMMA")
      (uTerms P i) (Dot.polyValues F) (Dot.polyValues G) Dot.gammaValues)
    (hsum : Dot.polySum (uTerms P i) F G = KPke.dotK (fun j => aMW true P L s₀ mB j i) (encY rv) P.k)
    (ht : Optimized.TransformTables s)
    (he : PolyIsW 16 s.mem (sA L s₀ (noiseOff P i)) (cbd rv (P.k+i))) :
    WP isa (Kem16.uRow P (slotReg kC) co i) s
      (EInvW true P L s₀ kC co mE mB v rv mv P.k (i+1)) := by
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
  have ht₁ := ht.frame sy₁ (e₁.kb.rd.trans h.kb.rd.symm) (e₁.kb.wr.trans h.kb.wr.symm) (e₁.kb.sp.trans h.kb.sp.symm)
    f₁ (cov_w hp h.kb ⟨hp.scw,hp.scb⟩ (o:=TP P) (l:=1024) (hp.fs (by lom)))
  refine WP.seq (WP.mono (invW_ok hp (po_TP hw) e₁.kb t₁.1 ht₁) fun s₂ ⟨kb₂,f₂,t₂,x₂⟩ => ?_)
  have e₂ := e₁.frame hp kb₂ x₂ f₂ (far_mul hp A (Nat.le_refl _) hn (by lom) (by lom))
  have p₂ : PolyIsW 16 s₂.mem _ _ := polyIsW_frame_poly (w16 := true) f₂ far p₁
  rw [t₁.2] at t₂
  refine WP.seq (WP.mono (addW_read_ok hp (po_TP hw) (Noise.noise_fits hr hi)
    (.inl (by lom)) e₂.kb t₂.1 p₂.1) fun s₃ ⟨kb₃,f₃,t₃,x₃⟩ => ?_)
  have e₃ := e₂.frame hp kb₃ x₃ f₃ (far_one hp A (Nat.le_refl _) hn (by lom) (by lom))
  rw [t₂.2,p₂.2] at t₃
  refine WP.seq (WP.mono (widenW_ok hp (po_TP hw) (po_PP hw) (.inl (by lom)) e₃.kb t₃)
    fun s₄ ⟨kb₄,f₄,t₄,x₄⟩ => ?_)
  have e₄ := e₃.frame hp kb₄ x₄ f₄ (far_one hp A (Nat.le_refl _) hn (by lom) (by lom))
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
  refine ⟨e₅.kb,e₅.x24,e₅.r,e₅.m,e₅.a,e₅.y,fun j hj => ?_,e₅.fr⟩
  rcases (by omega : j<i ∨ j=i) with hj | rfl
  · exact e₅.u j hj
  · rw [b₅,t₄.2]; rfl

theorem ErrorsW.frame_enc {s₀ s t : State} (hp : Pre P L s₀) (hr : Noise.Room P)
    {kE eo kC co : Nat} (A : EncArgs P L kE eo kC co) {rv : List Byte}
    (h : ErrorsW P L s₀ rv s) (hf : Frame (encW P L s₀ kC co) s.mem t.mem) : ErrorsW P L s₀ rv t := by
  intro j hj
  exact polyIsW_frame_poly (w16 := true) hf (encW_noise_far hp hr A hj) (h j hj)

theorem u_rowsW {s₀ s : State} (hp : Pre P L s₀) (hr : Noise.Room P) (hc : Calls P)
    {kE eo kC co : Nat} (A : EncArgs P L kE eo kC co)
    {mB : Mem} {v : BitVec 64} {rv mv : List Byte}
    (htr : Optimized.TransformTables s)
    (h : EInvW true P L s₀ kC co s.mem mB v rv mv P.k 0 s) (he : ErrorsW P L s₀ rv s)
    (ht : Dot.GammaArtifact s.mem (s.syms "VG_MLKEM_GAMMA"))
    (hcT : Covers [⟨s.syms "VG_MLKEM_GAMMA",512⟩] (s.rd++s.wr))
    (ha : ∀r∈encW P L s₀ kC co, (⟨s.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint r) :
    WPs ((List.range P.k).map (Kem16.uRow P (slotReg kC) co)) s
      (fun t => EInvW true P L s₀ kC co s.mem mB v rv mv P.k P.k t ∧ t.syms=s.syms) := by
  apply WPs.range (I := fun i t => EInvW true P L s₀ kC co s.mem mB v rv mv P.k i t ∧ t.syms=s.syms)
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
    exact WP.mono_syms (fused_u_rowW hp hr hc A hi ei (u_readyW hp hi ei gt ct da).data
      (u_sumW hi ei) (transform_enc_frame hp A h.kb ei.kb htr hs ei.fr) (et i hi)) fun u hu hsu => ⟨hu,hsu.trans hs⟩
  · exact ⟨h,rfl⟩

end VG.Proof.MlKem.AArch64.Kem
