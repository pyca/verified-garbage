module

public import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.Noise
public import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.VRest
public import VerifiedGarbage.Impl.MlKem.AArch64.Kem16P
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemVDecode
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Lists
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemUContext
import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.Ops
import VerifiedGarbage.Proof.Framework.AArch64.Syms
public import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.Noise
import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.URow
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemTransformFrames
public import VerifiedGarbage.Impl.MlKem.AArch64.Kem16
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Layout
public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Table
public import VerifiedGarbage.Proof.MlKem.AArch64.DotW.Loop
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemURow

/-! ### `MlKem.AArch64.Kem16P.VRest`, which only this module used -/

section

/-! # `v` with `e₂` from the matrix

`v_restP`: `Kem16P.vRestP`, which computes `e₂` with `prf` as `Kem16.vRest`
does (`v_restW`), or, when the matrix computed it (`e2`), finds it at `EP`
(`v_restE`, as `v_restW` with `e₂` kept through the decoding, the dot product
and the inverse transform). -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Kem
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
variable {P : KemLay} {L : Layout}

theorem v_tailE {s₀ s : State} (hp : Pre P L s₀)
    (hc : Calls P) {kE eo kC co : Nat} (A : EncArgs P L kE eo kC co)
    {mE mB : Mem} {v : BitVec 64} {rv mv : List Byte} {T : Nat → Poly}
    (e₀ : VInvW P L s₀ kC co mE mB v rv mv P.k P.k s)
    (ht : Optimized.TransformTables s)
    (t₀ : PolyIsW 16 s.mem (sA L s₀ (TP P)) (KPke.dotK T (encY rv) P.k))
    (e2 : PolyIsW 16 s.mem (sA L s₀ (EP P)) (cbd rv (2 * P.k))) :
    WPs [Ntt16.Readonly.nttInvAtWithW (TP P) NS,.block [],Kem16.addWAt (TP P) (EP P),
      Kem16.widenAt (TP P) (PP P),ddAt .x28 MB 1 (EP P),addAt (PP P) (EP P),
      P.ceLAt (PP P) P.dv (slotReg kC) (co+32*P.du*P.k)] s
      (fun t => VInvW P L s₀ kC co mE mB v rv mv P.k P.k t ∧
        bytesAt t.mem (kA s₀ (L.slot kC)+BitVec.ofNat 64 (co+32*P.du*P.k)) (32*P.dv)=
          compressEncode P.dv (vPoly P T rv mv)) := by
  have hw := hp.wf
  refine WPs.cons (WP.mono (invW_ok hp (po_TP hw) e₀.kb t₀.1 ht) fun s₁ ⟨kb₁, f₁, t₁, x₁⟩ => ?_)
  obtain e₁ := e₀.frame_far hp kb₁ x₁ f₁ (far_mul hp A (Nat.le_refl _) (Nat.le_refl _) (by lom) (by lom))
  rw [t₀.2] at t₁
  obtain p₂ : PolyIsW 16 s₁.mem (sA L s₀ (EP P)) (cbd rv (2 * P.k)) :=
    polyIsW_frame_poly (w16 := true) f₁ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact papart hp (po_EP hw) (po_TP hw) (by lom)
      · exact sdisj hp (po_EP hw).le (by lom) (by lom)) e2
  refine WPs.cons (wp_nil ?_)
  have kb₂ := kb₁
  have e₂ := e₁
  have t₂ := t₁
  refine WPs.cons (WP.mono (addW_read_ok hp (po_TP hw) (by lom) (.inr (by lom)) kb₂ t₂.1 p₂.1)
    fun s₃ ⟨kb₃, f₃, t₃, x₃⟩ => ?_)
  obtain e₃ := e₂.frame_far hp kb₃ x₃ f₃ (far_one hp A (Nat.le_refl _) (Nat.le_refl _) (by lom) (by lom))
  rw [t₂.2, p₂.2] at t₃
  refine WPs.cons (WP.mono (widenW_ok hp (po_TP hw) (po_PP hw) (.inl (by lom)) e₃.kb t₃)
    fun s₄ ⟨kb₄, f₄, t₄, x₄⟩ => ?_)
  obtain e₄ := e₃.frame_far hp kb₄ x₄ f₄ (far_one hp A (Nat.le_refl _) (Nat.le_refl _) (by lom) (by lom))
  refine WPs.cons (WP.mono (dd_ok hp (k := 3) (o := MB) (d := 1) (off := EP P) (by decide)
    (hp.fs (by lom)) (by decide) (po_EP hw) (.inr (.inl (by lom))) e₄.kb)
    fun s₅ ⟨kb₅, f₅, p₅, x₅⟩ => ?_)
  obtain e₅ := e₄.frame_far hp kb₅ x₅ f₅ (far_one hp A (Nat.le_refl _) (Nat.le_refl _) (by lom) (by lom))
  obtain t₅ := polyIs_frame f₅ (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact papart hp (po_PP hw) (po_EP hw) (by lom)) t₄
  have hm : bytesAt s₄.mem (kA s₀ (L.slot 3) + BitVec.ofNat 64 MB) (32 * 1) = mv := e₄.m
  rw [hm] at p₅
  refine WPs.cons (WP.mono (add_ok hp (po_PP hw) (po_EP hw) (.inr (by lom)) e₅.kb t₅.1 p₅.1)
    fun s₆ ⟨kb₆, f₆, t₆, x₆⟩ => ?_)
  obtain e₆ := e₅.frame_far hp kb₆ x₆ f₆ (far_one hp A (Nat.le_refl _) (Nat.le_refl _) (by lom) (by lom))
  rw [t₅.2, p₅.2] at t₆
  have fC := A.fC
  obtain hmk := Nat.mul_assoc 32 P.du P.k
  refine WPs.single (WP.mono (ceL_ok hp hc (off := PP P) (d := P.dv) (k := kC) (o := co + 32 * P.du * P.k)
    (po_PP hw) (.inr rfl) A.hkC A.wC (by lom) (by
      rcases A.sC with hC | hC
      · exact .inl hC
      · exact .inr ⟨by subst hC; lom, .inr (by subst hC; lom)⟩)
    e₆.kb t₆.1) fun s₇ ⟨kb₇, f₇, b₇, x₇⟩ => ?_)
  refine ⟨e₆.frame_far hp kb₇ x₇ f₇ fun r hr => by
    rw [List.mem_singleton.mp hr]; exact far_ct hp A (Nat.le_refl _) (by lom), ?_⟩
  rw [b₇, t₆.2]

theorem v_restE {prf : Nat→Nat→Prog isa} {s₀ s : State} (hp : Pre P L s₀)
    (hc : Calls P) {kE eo kC co : Nat} (A : EncArgs P L kE eo kC co)
    {mE mB : Mem} {v : BitVec 64} {rv mv : List Byte} {T : Nat → Poly}
    (hT : ∀j<P.k, decode12 (bytesAt s₀.mem (kA s₀ (L.slot kE)+BitVec.ofNat 64 (eo+384*j)) 384)=T j)
    (htr : Optimized.TransformTables s)
    (h : VInvW P L s₀ kC co mE mB v rv mv P.k P.k s)
    (ht : Dot.GammaArtifact s.mem (s.syms "VG_MLKEM_GAMMA"))
    (hcT : Covers [⟨s.syms "VG_MLKEM_GAMMA",512⟩] (s.rd++s.wr))
    (ha : ∀r∈encW P L s₀ kC co, (⟨s.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint r)
    (e2 : PolyIsW 16 s.mem (sA L s₀ (EP P)) (cbd rv (2 * P.k))) :
    WP isa (Impl.MlKem.AArch64.Kem16P.vRestP prf P true (slotReg kE) eo .x28 MB (slotReg kC) co) s
      (fun t => VInvW P L s₀ kC co mE mB v rv mv P.k P.k t ∧
        bytesAt t.mem (kA s₀ (L.slot kC)+BitVec.ofNat 64 (co+32*P.du*P.k)) (32*P.dv)=
          compressEncode P.dv (vPoly P T rv mv)) := by
  have hw := hp.wf
  apply WPs.seqs (by simp)
  apply WPs.append
  refine WPs.mono_syms (v_decodeW hp A hT h) fun t ⟨vt,dt⟩ hs => ?_
  obtain ga : ∀r∈[R (kA s₀) L.sc AH (1024*P.k)],
      (⟨s.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint r := by
    intro r hh
    rw [List.mem_singleton.mp hh]
    obtain ⟨r',hm,hh'⟩ := (firstRow_vfar hp A).2.2.2.2
    exact (ha r' hm).sub_right hh'
  obtain gt : Dot.GammaArtifact t.mem (t.syms "VG_MLKEM_GAMMA") := by
    rw [hs]; exact gamma_frame ht dt.frame ga
  obtain ct : Covers [⟨t.syms "VG_MLKEM_GAMMA",512⟩] (t.rd++t.wr) := by
    simpa only [hs,dt.kb.rd,dt.kb.wr,←h.kb.rd,←h.kb.wr] using hcT
  obtain da : (polyRegion (sA L s₀ (TP P))).Disjoint ⟨t.syms "VG_MLKEM_GAMMA",512⟩ := by
    rw [hs]
    exact ((ha (R (kA s₀) L.sc PB (SV P-PB)) (by simp [encW])).sub_right
      (R.sub2 (by lom) (by lom))).symm
  obtain trt := htr.frame hs (dt.kb.rd.trans h.kb.rd.symm) (dt.kb.wr.trans h.kb.wr.symm)
    (dt.kb.sp.trans h.kb.sp.symm) dt.frame (cov_w hp h.kb ⟨hp.scw,hp.scb⟩ (hp.fs (by lom)))
  refine WPs.cons (WP.mono_syms (fusedW_ok hp (po_TP hw) dt.kb (decodedTerms P)
    (decoded_readyW hp dt gt ct da).data) fun u ⟨ku,fu,pu,xu⟩ hsu => ?_)
  rw [decoded_sum] at pu
  obtain vu := vt.frame_far hp ku xu fu (far_one hp A (Nat.le_refl _) (Nat.le_refl _) (by lom) (by lom))
  obtain tru := trt.frame hsu (ku.rd.trans dt.kb.rd.symm) (ku.wr.trans dt.kb.wr.symm)
    (ku.sp.trans dt.kb.sp.symm) fu (cov_w hp dt.kb ⟨hp.scw,hp.scb⟩ (hp.fs (by lom)))
  obtain e2t : PolyIsW 16 t.mem (sA L s₀ (EP P)) (cbd rv (2 * P.k)) :=
    polyIsW_frame_poly (w16 := true) dt.frame (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact sdisj hp (po_EP hw).le (by lom) (by lom)) e2
  obtain e2u : PolyIsW 16 u.mem (sA L s₀ (EP P)) (cbd rv (2 * P.k)) :=
    polyIsW_frame_poly (w16 := true) fu (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact papart hp (po_EP hw) (po_TP hw) (by lom)) e2t
  exact v_tailE hp hc A vu tru pu e2u

theorem v_restP {prf : Nat→Nat→Prog isa} (valid : PrfValidW P L prf) {s₀ s : State} (hp : Pre P L s₀)
    (hc : Calls P) {kE eo kC co : Nat} (A : EncArgs P L kE eo kC co) (e2 : Bool)
    {mE mB : Mem} {v : BitVec 64} {rv mv : List Byte} {T : Nat → Poly}
    (hT : ∀j<P.k, decode12 (bytesAt s₀.mem (kA s₀ (L.slot kE)+BitVec.ofNat 64 (eo+384*j)) 384)=T j)
    (htr : Optimized.TransformTables s)
    (h : VInvW P L s₀ kC co mE mB v rv mv P.k P.k s)
    (ht : Dot.GammaArtifact s.mem (s.syms "VG_MLKEM_GAMMA"))
    (hcT : Covers [⟨s.syms "VG_MLKEM_GAMMA",512⟩] (s.rd++s.wr))
    (ha : ∀r∈encW P L s₀ kC co, (⟨s.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint r)
    (he : e2 = true → PolyIsW 16 s.mem (sA L s₀ (EP P)) (cbd rv (2 * P.k))) :
    WP isa (Impl.MlKem.AArch64.Kem16P.vRestP prf P e2 (slotReg kE) eo .x28 MB (slotReg kC) co) s
      (fun t => VInvW P L s₀ kC co mE mB v rv mv P.k P.k t ∧
        bytesAt t.mem (kA s₀ (L.slot kC)+BitVec.ofNat 64 (co+32*P.du*P.k)) (32*P.dv)=
          compressEncode P.dv (vPoly P T rv mv)) := by
  cases e2
  · exact v_restW valid hp hc A hT htr h ht hcT ha
  · exact v_restE hp hc A hT htr h ht hcT ha (he rfl)

end VG.Proof.MlKem.AArch64.Kem

end

end

/-! ### `MlKem.AArch64.Kem16P.URow`, which only this module used -/

section

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
  obtain hn : i≤P.k := Nat.le_of_lt hi
  obtain ef : noiseOff P i+1024≤L.len L.sc := by rw [hp.scl]; exact Noise.noise_fits hr hi
  obtain ep := Noise.noise_past_kem hr i
  obtain far : ∀r∈[R (kA s₀) L.sc (TP P) 1024,R (kA s₀) L.sc NS 1024],
      (polyRegion (sA L s₀ (noiseOff P i))).Disjoint r := by
    intro r hh
    rcases mem2' hh with rfl | rfl <;>
      exact hp.args.rdisj hp.scb hp.scb ef (hp.fs (by lom)) (.inl rfl) (.inr (.inr (by lom)))
  simp only [Kem16.uRow, seqs]
  refine WP.seq (WP.mono_syms (WP.mono (fusedW_ok hp (po_TP hw) h.kb (uTerms P i) hd)
    fun t ⟨kt,ft,pt,xt⟩ => (⟨h.frame hp kt xt ft (far_one hp A (Nat.le_refl _) hn (by lom) (by lom)),ft,pt⟩ :
      EInvW true P L s₀ kC co mE mB v rv mv P.k i t ∧ _ ∧ _)) fun s₁ ⟨e₁,f₁,t₁⟩ sy₁ => ?_)
  obtain p₁ : PolyIsW 16 s₁.mem _ _ := polyIsW_frame_poly (w16 := true) f₁
    (fun r hh => far r (by rw [List.mem_singleton.mp hh]; exact List.mem_cons_self ..)) he
  rw [hsum] at t₁
  obtain q₁ : PolyIsW 16 s₁.mem _ _ := polyIsW_frame_poly (w16 := true) f₁ (fun r hh => by
    rw [List.mem_singleton.mp hh]; exact papart hp (po_EP hw) (po_TP hw) (by lom)) hE
  obtain ht₁ := ht.frame sy₁ (e₁.kb.rd.trans h.kb.rd.symm) (e₁.kb.wr.trans h.kb.wr.symm) (e₁.kb.sp.trans h.kb.sp.symm)
    f₁ (cov_w hp h.kb ⟨hp.scw,hp.scb⟩ (o:=TP P) (l:=1024) (hp.fs (by lom)))
  refine WP.seq (WP.mono (invW_ok hp (po_TP hw) e₁.kb t₁.1 ht₁) fun s₂ ⟨kb₂,f₂,t₂,x₂⟩ => ?_)
  obtain e₂ := e₁.frame hp kb₂ x₂ f₂ (far_mul hp A (Nat.le_refl _) hn (by lom) (by lom))
  obtain p₂ : PolyIsW 16 s₂.mem _ _ := polyIsW_frame_poly (w16 := true) f₂ far p₁
  rw [t₁.2] at t₂
  obtain q₂ : PolyIsW 16 s₂.mem _ _ := polyIsW_frame_poly (w16 := true) f₂ (fun r hh => by
    rcases mem2' hh with rfl | rfl
    · exact papart hp (po_EP hw) (po_TP hw) (by lom)
    · exact sdisj hp (po_EP hw).le (by lom) (by lom)) q₁
  refine WP.seq (WP.mono (addW_read_ok hp (po_TP hw) (Noise.noise_fits hr hi)
    (.inl (by lom)) e₂.kb t₂.1 p₂.1) fun s₃ ⟨kb₃,f₃,t₃,x₃⟩ => ?_)
  obtain e₃ := e₂.frame hp kb₃ x₃ f₃ (far_one hp A (Nat.le_refl _) hn (by lom) (by lom))
  rw [t₂.2,p₂.2] at t₃
  obtain q₃ : PolyIsW 16 s₃.mem _ _ := polyIsW_frame_poly (w16 := true) f₃ (fun r hh => by
    rw [List.mem_singleton.mp hh]; exact papart hp (po_EP hw) (po_TP hw) (by lom)) q₂
  refine WP.seq (WP.mono (widenW_ok hp (po_TP hw) (po_PP hw) (.inl (by lom)) e₃.kb t₃)
    fun s₄ ⟨kb₄,f₄,t₄,x₄⟩ => ?_)
  obtain e₄ := e₃.frame hp kb₄ x₄ f₄ (far_one hp A (Nat.le_refl _) hn (by lom) (by lom))
  obtain q₄ : PolyIsW 16 s₄.mem _ _ := polyIsW_frame_poly (w16 := true) f₄ (fun r hh => by
    rw [List.mem_singleton.mp hh]; exact papart hp (po_EP hw) (po_PP hw) (by lom)) q₃
  have fC := A.fC
  obtain hu := du_le hi
  refine WP.mono (ceL_ok hp hc (off := PP P) (d := P.du) (k := kC) (o := co+32*P.du*i)
    (po_PP hw) (.inl rfl) A.hkC A.wC (by lom) (by
      rcases A.sC with hC | hC
      · exact .inl hC
      · exact .inr ⟨by subst hC; lom,.inr (by subst hC; lom)⟩)
    e₄.kb t₄.1) fun s₅ ⟨kb₅,f₅,b₅,x₅⟩ => ?_
  obtain e₅ := e₄.frame hp kb₅ x₅ f₅ fun r hh => by
    rw [List.mem_singleton.mp hh]; exact far_ct hp A (Nat.le_refl _) (by lom)
  obtain q₅ : PolyIsW 16 s₅.mem _ _ := polyIsW_frame_poly (w16 := true) f₅ (fun r hh => by
    rw [List.mem_singleton.mp hh]
    refine hp.args.rdisj hp.scb (hp.lt A.hkC) (hp.fs (po_EP hw).le) (by lom) (.inr (.inr A.wC)) ?_
    rcases A.sC with hC | hC
    · exact .inl (Ne.symm hC)
    · subst hC; exact .inr (.inl (by lom))) q₄
  refine ⟨⟨e₅.kb,e₅.x24,e₅.r,e₅.m,e₅.a,e₅.y,fun j hj => ?_,e₅.fr⟩, q₅⟩
  rcases (by omega_using [hj] : j<i ∨ j=i) with hj | rfl
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
    obtain et := he.frame_enc hp hr A ei.fr
    obtain gt : Dot.GammaArtifact t.mem (t.syms "VG_MLKEM_GAMMA") := by
      rw [hs]; exact gamma_frame ht ei.fr ha
    obtain ct : Covers [⟨t.syms "VG_MLKEM_GAMMA",512⟩] (t.rd++t.wr) := by
      simpa only [hs,ei.kb.rd,ei.kb.wr,←h.kb.rd,←h.kb.wr] using hcT
    obtain da : (polyRegion (sA L s₀ (TP P))).Disjoint ⟨t.syms "VG_MLKEM_GAMMA",512⟩ := by
      rw [hs]
      have hw := hp.wf
      obtain hsub : Region.Sub (R (kA s₀) L.sc (TP P) 1024) (R (kA s₀) L.sc PB (SV P-PB)) :=
        R.sub2 (by lom) (by lom)
      exact ((ha _ (by simp [encW])).sub_right hsub).symm
    exact WP.mono_syms (fused_u_rowE hp hr hc A hi ei (u_readyW hp hi ei gt ct da).data
      (u_sumW hi ei) (transform_enc_frame hp A h.kb ei.kb htr hs ei.fr) (et i hi) qi)
      fun u ⟨hu,qu⟩ hsu => ⟨hu,hsu.trans hs,qu⟩
  · exact ⟨h,rfl,hE⟩

end VG.Proof.MlKem.AArch64.Kem

end

end


/-! # The 16-bit encryption after the matrix computed PRF outputs

`encrypt_restP`: `Kem16P.encryptRestP`, the noise from the buffers
(`noiseP_ok`), then the rows of `u` and `v` (`after_noiseP`). -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Kem16P
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem
variable {P : KemLay} {L : Layout}
variable {prf : Nat→Nat→Prog isa}

/-- The rows of `u` and `v`, `e₂` at `EP` already if `e2`. -/
theorem after_noiseP (valid : PrfValidW P L prf) {s₀ s : State} (hp : Pre P L s₀) (hr : Noise.Room P)
    (hc : Calls P) {kE eo kC co : Nat} (A : EncArgs P L kE eo kC co) (e2 : Bool)
    {mB : Mem} {v : BitVec 64} {rv mv : List Byte} {T : Nat → Poly}
    (hT : ∀j<P.k, decode12 (bytesAt s₀.mem (kA s₀ (L.slot kE)+BitVec.ofNat 64 (eo+384*j)) 384)=T j)
    (htr : Optimized.TransformTables s)
    (h : EInvW true P L s₀ kC co s.mem mB v rv mv P.k 0 s) (he : ErrorsW P L s₀ rv s)
    (ht : Dot.GammaArtifact s.mem (s.syms "VG_MLKEM_GAMMA"))
    (hcT : Covers [⟨s.syms "VG_MLKEM_GAMMA",512⟩] (s.rd++s.wr))
    (ha : ∀r∈encW P L s₀ kC co, (⟨s.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint r)
    (hE : e2 = true → PolyIsW 16 s.mem (sA L s₀ (EP P)) (cbd rv (2 * P.k))) :
    WP isa (seqs (((List.range P.k).map (Kem16.uRow P (slotReg kC) co)) ++
      [Impl.MlKem.AArch64.Kem16P.vRestP prf P e2 (slotReg kE) eo .x28 MB (slotReg kC) co])) s
      (fun t => VInvW P L s₀ kC co s.mem mB v rv mv P.k P.k t ∧
        bytesAt t.mem (kA s₀ (L.slot kC)+BitVec.ofNat 64 (co+32*P.du*P.k)) (32*P.dv)=
          compressEncode P.dv (vPoly P T rv mv)) := by
  apply WPs.seqs (by simp)
  apply WPs.append
  cases e2
  · refine WPs.mono (u_rowsW hp hr hc A htr h he ht hcT ha) fun t ⟨et,hs⟩ => ?_
    obtain gt : Dot.GammaArtifact t.mem (t.syms "VG_MLKEM_GAMMA") := by
      rw [hs]; exact gamma_frame ht et.fr ha
    obtain ct : Covers [⟨t.syms "VG_MLKEM_GAMMA",512⟩] (t.rd++t.wr) := by
      simpa only [hs,et.kb.rd,et.kb.wr,←h.kb.rd,←h.kb.wr] using hcT
    exact WPs.single (v_restP valid hp hc A false hT (transform_enc_frame hp A h.kb et.kb htr hs et.fr)
      et.vinv gt ct (by simpa only [hs] using ha) (fun h => absurd h (by decide)))
  · refine WPs.mono (u_rowsE hp hr hc A htr h he ht hcT ha (hE rfl)) fun t ⟨et,hs,qt⟩ => ?_
    obtain gt : Dot.GammaArtifact t.mem (t.syms "VG_MLKEM_GAMMA") := by
      rw [hs]; exact gamma_frame ht et.fr ha
    obtain ct : Covers [⟨t.syms "VG_MLKEM_GAMMA",512⟩] (t.rd++t.wr) := by
      simpa only [hs,et.kb.rd,et.kb.wr,←h.kb.rd,←h.kb.wr] using hcT
    exact WPs.single (v_restP valid hp hc A true hT (transform_enc_frame hp A h.kb et.kb htr hs et.fr)
      et.vinv gt ct (by simpa only [hs] using ha) (fun _ => qt))

/-- What the noise writes, `scratch` may be written. -/
theorem noiseW_cov {s₀ s : State} (hp : Pre P L s₀) (hr : Noise.Room P) (h : KB P L s₀ s) :
    Covers (noiseW P L s₀) s.wr := by
  have hw := hp.wf
  refine Covers.cons (cov_s hp h (by lom)) (Covers.cons (cov_s hp h (by lom)) (Covers.cons ?_ Covers.nil))
  refine cov_w hp h ⟨hp.scw, hp.scb⟩ ?_
  rw [hp.scl]; have := Noise.noise_fits (P := P) hr (i := P.k - 1) (by have := hw.facts; omega_using [this])
  simp only [Impl.MlKem.AArch64.Noise.noiseOff] at this ⊢; have := hw.facts; omega_arith

/-- **The noise, `u` and `v`**, the first `n ≥ 2k` PRF outputs in their buffers. -/
theorem encrypt_restP (valid : PrfValidW P L prf) {s₀ s : State} (hp : Pre P L s₀) (hr : Noise.Room P)
    (hc : Calls P) {kE eo kC co : Nat} (A : EncArgs P L kE eo kC co) {n : Nat} (hn : 2 * P.k ≤ n)
    {mE mB : Mem} {v : BitVec 64} {rv mv : List Byte} {T : Nat → Poly}
    (hT : ∀j<P.k, decode12 (bytesAt s₀.mem (kA s₀ (L.slot kE)+BitVec.ofNat 64 (eo+384*j)) 384)=T j)
    (htr : Optimized.TransformTables s)
    (h : EInvW true P L s₀ kC co mE mB v rv mv 0 0 s)
    (ht : Dot.GammaArtifact s.mem (s.syms "VG_MLKEM_GAMMA"))
    (hcT : Covers [⟨s.syms "VG_MLKEM_GAMMA",512⟩] (s.rd++s.wr))
    (ha : ∀r∈encW P L s₀ kC co, (⟨s.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint r)
    (hn' : ∀r∈noiseW P L s₀, (⟨s.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint r)
    (hprf : ∀ N < min n (Impl.MlKem.AArch64.Kem16P.prfs P), PrfAt P L s₀ s.mem s.mem N) :
    WP isa (Impl.MlKem.AArch64.Kem16P.encryptRestP prf P n (slotReg kE) eo .x28 MB (slotReg kC) co) s
      (fun t => ∃mN, Frame (noiseW P L s₀) s.mem mN ∧
        VInvW P L s₀ kC co mN mB v rv mv P.k P.k t ∧
        bytesAt t.mem (kA s₀ (L.slot kC)+BitVec.ofNat 64 (co+32*P.du*P.k)) (32*P.dv)=
          compressEncode P.dv (vPoly P T rv mv)) := by
  have hw := hp.wf
  have hk := hw.facts
  refine WP.seq (WP.mono (noiseP_ok (prf := prf) hp hr h.kb htr hn h.r hprf) fun t nt => ?_)
  obtain hcnt : 2 * P.k ≤ min n (Impl.MlKem.AArch64.Kem16P.prfs P) := by
    simp only [Impl.MlKem.AArch64.Kem16P.prfs]; omega_using [hn]
  obtain far : ∀ {o l : Nat}, o + l ≤ SV P + 48 →
      (o + l ≤ NS ∨ (NS + 1024 ≤ o ∧ o + l ≤ YH P) ∨ TP P ≤ o) →
      ∀ r ∈ noiseW P L s₀, (R (kA s₀) L.sc o l).Disjoint r := fun hf ho => noiseW_far hp hr hf ho
  obtain e0 : EInvW true P L s₀ kC co t.mem mB v rv mv P.k 0 t := by
    refine ⟨nt.kb, nt.x24.trans h.x24, ?_, ?_, fun i hi j hj => ?_, fun j hj => ?_,
      fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _⟩
    · rw [bytesAt_frame nt.fr (far (o := RB) (l := 32) (by lom) (.inl (by lom))) (by decide)]; exact h.r
    · rw [bytesAt_frame nt.fr (far (o := MB) (l := 32) (by lom) (.inl (by lom))) (by decide)]; exact h.m
    · have := ij_lt hi hj
      obtain fa := far (o := aOff P i j) (l := 1024) (by lom) (.inr (.inl ⟨by lom, by lom⟩))
      exact ⟨reducedW_frame nt.fr fa (h.a i hi j hj).1, (polyAtW_frame nt.fr fa).trans (h.a i hi j hj).2⟩
    · have d := nt.done j (by omega_using [hcnt, hj])
      simp only [Impl.MlKem.AArch64.Kem16P.target, tPoly, ite_eq_left hj] at d
      exact d
  obtain er : ErrorsW P L s₀ rv t := by
    intro j hj
    obtain d := nt.done (P.k + j) (by omega_using [hcnt, hj])
    simp only [Impl.MlKem.AArch64.Kem16P.target, tPoly, ite_eq_right (show ¬ P.k + j < P.k by omega_using []),
      ite_eq_left (show P.k + j < 2 * P.k by omega_using [hj]), Nat.add_sub_cancel_left] at d
    exact d
  obtain hE : decide (Impl.MlKem.AArch64.Kem16P.prfs P ≤ n) = true →
      PolyIsW 16 t.mem (sA L s₀ (EP P)) (cbd rv (2 * P.k)) := by
    intro he
    obtain he' : Impl.MlKem.AArch64.Kem16P.prfs P ≤ n := of_decide_eq_true he
    obtain d := nt.done (2 * P.k) (by simp only [Impl.MlKem.AArch64.Kem16P.prfs] at he' ⊢; omega_using [he'])
    simp only [Impl.MlKem.AArch64.Kem16P.target, tPoly, ite_eq_right (show ¬ 2 * P.k < P.k by omega_using []),
      Nat.lt_irrefl, ite_false] at d
    exact d
  obtain gt : Dot.GammaArtifact t.mem (t.syms "VG_MLKEM_GAMMA") := by
    rw [nt.syms]; exact gamma_frame ht nt.fr hn'
  obtain ct : Covers [⟨t.syms "VG_MLKEM_GAMMA",512⟩] (t.rd++t.wr) := by
    simpa only [nt.syms, nt.kb.rd, nt.kb.wr, ← h.kb.rd, ← h.kb.wr] using hcT
  obtain tt := htr.frame nt.syms (nt.kb.rd.trans h.kb.rd.symm) (nt.kb.wr.trans h.kb.wr.symm)
    (nt.kb.sp.trans h.kb.sp.symm) nt.fr (noiseW_cov hp hr h.kb)
  exact WP.mono (after_noiseP valid hp hr hc A _ hT tt e0 er gt ct (by simpa only [nt.syms] using ha) hE)
    fun u ⟨eu, vu⟩ => ⟨t.mem, nt.fr, eu, vu⟩

end VG.Proof.MlKem.AArch64.Kem16P
