module

public import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.VRest
public import VerifiedGarbage.Impl.MlKem.AArch64.Kem16P
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemVDecode
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Lists
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemUContext
import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.Ops
import VerifiedGarbage.Proof.Framework.AArch64.Syms

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
  have e₁ := e₀.frame_far hp kb₁ x₁ f₁ (far_mul hp A (Nat.le_refl _) (Nat.le_refl _) (by lom) (by lom))
  rw [t₀.2] at t₁
  have p₂ : PolyIsW 16 s₁.mem (sA L s₀ (EP P)) (cbd rv (2 * P.k)) :=
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
  have e₃ := e₂.frame_far hp kb₃ x₃ f₃ (far_one hp A (Nat.le_refl _) (Nat.le_refl _) (by lom) (by lom))
  rw [t₂.2, p₂.2] at t₃
  refine WPs.cons (WP.mono (widenW_ok hp (po_TP hw) (po_PP hw) (.inl (by lom)) e₃.kb t₃)
    fun s₄ ⟨kb₄, f₄, t₄, x₄⟩ => ?_)
  have e₄ := e₃.frame_far hp kb₄ x₄ f₄ (far_one hp A (Nat.le_refl _) (Nat.le_refl _) (by lom) (by lom))
  refine WPs.cons (WP.mono (dd_ok hp (k := 3) (o := MB) (d := 1) (off := EP P) (by decide)
    (hp.fs (by lom)) (by decide) (po_EP hw) (.inr (.inl (by lom))) e₄.kb)
    fun s₅ ⟨kb₅, f₅, p₅, x₅⟩ => ?_)
  have e₅ := e₄.frame_far hp kb₅ x₅ f₅ (far_one hp A (Nat.le_refl _) (Nat.le_refl _) (by lom) (by lom))
  have t₅ := polyIs_frame f₅ (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact papart hp (po_PP hw) (po_EP hw) (by lom)) t₄
  have hm : bytesAt s₄.mem (kA s₀ (L.slot 3) + BitVec.ofNat 64 MB) (32 * 1) = mv := e₄.m
  rw [hm] at p₅
  refine WPs.cons (WP.mono (add_ok hp (po_PP hw) (po_EP hw) (.inr (by lom)) e₅.kb t₅.1 p₅.1)
    fun s₆ ⟨kb₆, f₆, t₆, x₆⟩ => ?_)
  have e₆ := e₅.frame_far hp kb₆ x₆ f₆ (far_one hp A (Nat.le_refl _) (Nat.le_refl _) (by lom) (by lom))
  rw [t₅.2, p₅.2] at t₆
  have fC := A.fC
  have hmk := Nat.mul_assoc 32 P.du P.k
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
  have ga : ∀r∈[R (kA s₀) L.sc AH (1024*P.k)],
      (⟨s.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint r := by
    intro r hh
    rw [List.mem_singleton.mp hh]
    obtain ⟨r',hm,hh'⟩ := (firstRow_vfar hp A).2.2.2.2
    exact (ha r' hm).sub_right hh'
  have gt : Dot.GammaArtifact t.mem (t.syms "VG_MLKEM_GAMMA") := by
    rw [hs]; exact gamma_frame ht dt.frame ga
  have ct : Covers [⟨t.syms "VG_MLKEM_GAMMA",512⟩] (t.rd++t.wr) := by
    simpa only [hs,dt.kb.rd,dt.kb.wr,←h.kb.rd,←h.kb.wr] using hcT
  have da : (polyRegion (sA L s₀ (TP P))).Disjoint ⟨t.syms "VG_MLKEM_GAMMA",512⟩ := by
    rw [hs]
    exact ((ha (R (kA s₀) L.sc PB (SV P-PB)) (by simp [encW])).sub_right
      (R.sub2 (by lom) (by lom))).symm
  have trt := htr.frame hs (dt.kb.rd.trans h.kb.rd.symm) (dt.kb.wr.trans h.kb.wr.symm)
    (dt.kb.sp.trans h.kb.sp.symm) dt.frame (cov_w hp h.kb ⟨hp.scw,hp.scb⟩ (hp.fs (by lom)))
  refine WPs.cons (WP.mono_syms (fusedW_ok hp (po_TP hw) dt.kb (decodedTerms P)
    (decoded_readyW hp dt gt ct da).data) fun u ⟨ku,fu,pu,xu⟩ hsu => ?_)
  rw [decoded_sum] at pu
  have vu := vt.frame_far hp ku xu fu (far_one hp A (Nat.le_refl _) (Nat.le_refl _) (by lom) (by lom))
  have tru := trt.frame hsu (ku.rd.trans dt.kb.rd.symm) (ku.wr.trans dt.kb.wr.symm)
    (ku.sp.trans dt.kb.sp.symm) fu (cov_w hp dt.kb ⟨hp.scw,hp.scb⟩ (hp.fs (by lom)))
  have e2t : PolyIsW 16 t.mem (sA L s₀ (EP P)) (cbd rv (2 * P.k)) :=
    polyIsW_frame_poly (w16 := true) dt.frame (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact sdisj hp (po_EP hw).le (by lom) (by lom)) e2
  have e2u : PolyIsW 16 u.mem (sA L s₀ (EP P)) (cbd rv (2 * P.k)) :=
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
