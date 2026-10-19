module

public import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.URow
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemVRestUsing

/-! # The 16-bit ciphertext component `v`

`v_restW`: `Kem16.vRest` decodes `t̂` from `ek` with 16 bits into the consumed
first row of the matrix (`v_decodeW`), takes its fused dot product with `ŷ`,
the inverse transform and the sum with `e₂` in 16 bits, widens the sum into
`PP` and adds the decompressed message there with 32 bits. -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Kem
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
variable {P : KemLay} {L : Layout}

/-- `VInv` with `ŷ` and `Â` stored with 16 bits. -/
structure VInvW (P : KemLay) (L : Layout) (s₀ : State) (kC co : Nat) (mE mB : Mem) (v : BitVec 64)
    (rv mv : List Byte) (nY nU : Nat) (s : State) : Prop where
  kb : KB P L s₀ s
  x24 : s.gpr .x24 = v
  r : bytesAt s.mem (sA L s₀ RB) 32 = rv
  m : bytesAt s.mem (sA L s₀ MB) 32 = mv
  y : ∀ j < nY, PolyIsW 16 s.mem (sA L s₀ (yOff P j)) (encY rv j)
  u : ∀ i < nU, bytesAt s.mem (kA s₀ (L.slot kC) + BitVec.ofNat 64 (co + 32 * P.du * i)) (32 * P.du) =
    compressEncode P.du (KPke.encU P.params (aMW true P L s₀ mB) rv i)
  fr : Frame (encW P L s₀ kC co) mE s.mem

theorem VInvW.frame {s₀ : State} (hp : Pre P L s₀) {kC co : Nat} {mE mB : Mem} {v : BitVec 64}
    {rv mv : List Byte} {nY nU : Nat} {s s' : State} (h : VInvW P L s₀ kC co mE mB v rv mv nY nU s)
    (hk : KB P L s₀ s') (hx : s'.gpr .x24 = s.gpr .x24) {W : List Region} (hf : Frame W s.mem s'.mem)
    (hW : ∀ r ∈ W, VFar P L s₀ kC co nY nU r) : VInvW P L s₀ kC co mE mB v rv mv nY nU s' := by
  have hw := hp.wf
  refine ⟨hk, by rw [hx, h.x24], ?_, ?_, fun j hj => ?_, fun i hi => ?_,
    h.fr.trans (hf.sub fun r hr => (hW r hr).2.2.2.2)⟩
  · rw [bytesAt_frame hf (fun r hr => (hW r hr).1) (by decide)]; exact h.r
  · rw [bytesAt_frame hf (fun r hr => (hW r hr).2.1) (by decide)]; exact h.m
  · exact polyIsW_frame_poly (w16 := true) hf (fun r hr => (hW r hr).2.2.1.sub_left
      (R.sub2 (by simp only [yOff]; omega) (by simp only [yOff]; omega))) (h.y j hj)
  · rw [bytesAt_frame hf (fun r hr => (hW r hr).2.2.2.1.sub_left
      (R.sub2 (by omega) (by have := mul_succ_le (a := 32 * P.du) hi; omega))) (by kom)]
    exact h.u i hi

theorem VInvW.frame_far {s₀ : State} (hp : Pre P L s₀) {kC co : Nat} {mE mB : Mem} {v : BitVec 64}
    {rv mv : List Byte} {nY nU : Nat} {s s' : State} (h : VInvW P L s₀ kC co mE mB v rv mv nY nU s)
    (hk : KB P L s₀ s') (hx : s'.gpr .x24=s.gpr .x24) {W : List Region} (hf : Frame W s.mem s'.mem)
    (hW : ∀r∈W, Far P L s₀ kC co nY nU r) : VInvW P L s₀ kC co mE mB v rv mv nY nU s' :=
  h.frame hp hk hx hf (fun r hr => (hW r hr).vfar)

theorem EInvW.vinv {s₀ s : State} {kC co : Nat} {mE mB : Mem} {v : BitVec 64}
    {rv mv : List Byte} {nY nU : Nat} (h : EInvW true P L s₀ kC co mE mB v rv mv nY nU s) :
    VInvW P L s₀ kC co mE mB v rv mv nY nU s :=
  ⟨h.kb,h.x24,h.r,h.m,h.y,h.u,h.fr⟩

/-- `DecodeInv` with 16 bits. -/
structure DecodeInvW (P : KemLay) (L : Layout) (s₀ : State) (mD : Mem)
    (T Y : Nat → Poly) (v : BitVec 64) (n : Nat) (s : State) : Prop where
  kb : KB P L s₀ s
  x24 : s.gpr .x24=v
  decoded : ∀ j<n, PolyIsW 16 s.mem (sA L s₀ (aOff P 0 j)) (T j)
  y : ∀ j<P.k, PolyIsW 16 s.mem (sA L s₀ (yOff P j)) (Y j)
  frame : Frame [R (kA s₀) L.sc AH (1024*n)] mD s.mem

theorem decode_stepW {s₀ s : State} (hp : Pre P L s₀) {kE eo : Nat}
    (hkE : kE<4) (hread : L.slot kE<L.nrd) (hfit : eo+384*P.k≤L.len (L.slot kE))
    {mD : Mem} {T Y : Nat → Poly} {v : BitVec 64} {j : Nat} (hj : j<P.k)
    (ht : ∀ i<P.k, decode12 (bytesAt s₀.mem (kA s₀ (L.slot kE)+BitVec.ofNat 64 (eo+384*i)) 384)=T i)
    (h : DecodeInvW P L s₀ mD T Y v j s) :
    WP isa (Kem16.dec12WAt (slotReg kE) (eo+384*j) (aOff P 0 j)) s (DecodeInvW P L s₀ mD T Y v (j+1)) := by
  have hw := hp.wf
  have h0 : 0<P.k := hw.facts.1
  have hs : L.slot kE ≠ L.sc := by have := hp.scw; omega
  have hmul := mul_succ_le (a := 384) hj
  refine WP.mono (dec12W_ok hp (k := kE) (o := eo+384*j) hkE (by omega)
    (po_a hw h0 hj) (.inl hs) h.kb) fun t ⟨kt,ft,pt,xt⟩ => ?_
  rw [h.kb.ro_bytes hread (by omega),ht j hj] at pt
  refine ⟨kt,xt.trans h.x24,?_,?_,?_⟩
  · intro i hi
    rcases (by omega : i<j ∨ i=j) with hi | rfl
    · exact polyIsW_frame_poly (w16 := true) ft (fun r hh => by
        rw [List.mem_singleton.mp hh]
        exact papart hp (po_a hw h0 (by omega)) (po_a hw h0 hj) (.inl (by lom))) (h.decoded i hi)
    · exact pt
  · intro i hi
    exact polyIsW_frame_poly (w16 := true) ft (fun r hh => by
      rw [List.mem_singleton.mp hh]
      exact papart hp (po_y hw hi) (po_a hw h0 hj) (.inr (by
        have := Nat.mul_le_mul_right P.k hw.facts.1
        lom))) (h.y i hi)
  · exact (h.frame.sub (fun r hh => by
      rw [List.mem_singleton.mp hh]
      exact ⟨_,List.mem_singleton_self _,R.sub2 (by omega) (by omega)⟩)).trans
      (ft.sub (fun r hh => by
        rw [List.mem_singleton.mp hh]
        exact ⟨_,List.mem_singleton_self _,R.sub2 (by simp [aOff]) (by simp [aOff]; omega)⟩))

theorem v_decodeW {s₀ s : State} (hp : Pre P L s₀) {kE eo kC co : Nat}
    (A : EncArgs P L kE eo kC co) {mE mB : Mem} {v : BitVec 64} {rv mv : List Byte} {T : Nat → Poly}
    (ht : ∀j<P.k, decode12 (bytesAt s₀.mem (kA s₀ (L.slot kE)+BitVec.ofNat 64 (eo+384*j)) 384)=T j)
    (h : VInvW P L s₀ kC co mE mB v rv mv P.k P.k s) :
    WPs ((List.range P.k).map fun j => Kem16.dec12WAt (slotReg kE) (eo+384*j) (aOff P 0 j)) s fun t =>
      VInvW P L s₀ kC co mE mB v rv mv P.k P.k t ∧
      DecodeInvW P L s₀ s.mem T (encY rv) v P.k t := by
  have hd : DecodeInvW P L s₀ s.mem T (encY rv) v 0 s :=
    ⟨h.kb,h.x24,fun _ hj => by omega,h.y,Frame.refl _ _⟩
  exact WPs.mono (WPs.range (fun _ hj _ h => decode_stepW hp A.hkE A.rE A.fE hj ht h) hd) fun t dt =>
    ⟨h.frame hp dt.kb (dt.x24.trans h.x24.symm) dt.frame (fun r hh => by
      rw [List.mem_singleton.mp hh]; exact firstRow_vfar hp A),dt⟩

theorem decoded_readyW {s₀ s : State} (hp : Pre P L s₀)
    {mD : Mem} {T Y : Nat → Poly} {v : BitVec 64}
    (h : DecodeInvW P L s₀ mD T Y v P.k s)
    (ht : Dot.GammaArtifact s.mem (s.syms "VG_MLKEM_GAMMA"))
    (hc : Covers [⟨s.syms "VG_MLKEM_GAMMA",512⟩] (s.rd++s.wr))
    (ha : (polyRegion (sA L s₀ (TP P))).Disjoint ⟨s.syms "VG_MLKEM_GAMMA",512⟩) :
    DotW.ReadyW s (s.gpr .x28+BitVec.ofNat 64 (TP P)) (s.syms "VG_MLKEM_GAMMA")
      (decodedTerms P) (decodedF T) (decodedG P Y) := by
  have hw := hp.wf
  have h0 : 0<P.k := hw.facts.1
  have term : ∀ fg∈decodedTerms P, ∃ j<P.k, fg=(aOff P 0 j,yOff P j) := by
    intro fg hh
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hh
    exact ⟨j,List.mem_range.mp hj,rfl⟩
  refine fused_readyW hp h.kb (po_TP hw) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ht hc ha
  · simpa only [decodedTerms,List.length_map,List.length_range] using hw.facts.2.1
  · intro fg hh; obtain ⟨j,hj,rfl⟩ := term fg hh; exact po_a hw h0 hj
  · intro fg hh; obtain ⟨j,hj,rfl⟩ := term fg hh; exact po_y hw hj
  · intro fg hh; obtain ⟨j,hj,rfl⟩ := term fg hh
    simpa only [decodedF,aOff,Nat.mul_zero,Nat.zero_add,Nat.add_sub_cancel_left,
      Nat.mul_div_cancel_left _ (by decide : 0<1024)] using h.decoded j hj
  · intro fg hh; obtain ⟨j,hj,rfl⟩ := term fg hh
    simpa only [decodedG,yOff,Nat.add_sub_cancel_left,
      Nat.mul_div_cancel_left _ (by decide : 0<1024)] using h.y j hj
  · intro fg hh; obtain ⟨j,hj,rfl⟩ := term fg hh
    have := ij_lt h0 hj
    exact .inr (by lom)
  · intro fg hh; obtain ⟨j,hj,rfl⟩ := term fg hh
    exact .inr (by lom)

theorem v_tailW {prf : Nat→Nat→Prog isa} (valid : PrfValidW P L prf) {s₀ s : State} (hp : Pre P L s₀)
    (hc : Calls P) {kE eo kC co : Nat} (A : EncArgs P L kE eo kC co)
    {mE mB : Mem} {v : BitVec 64} {rv mv : List Byte} {T : Nat → Poly}
    (e₀ : VInvW P L s₀ kC co mE mB v rv mv P.k P.k s)
    (ht : Optimized.TransformTables s)
    (t₀ : PolyIsW 16 s.mem (sA L s₀ (TP P)) (KPke.dotK T (encY rv) P.k)) :
    WPs [Ntt16.Readonly.nttInvAtWithW (TP P) NS,prf (2*P.k) (EP P),Kem16.addWAt (TP P) (EP P),
      Kem16.widenAt (TP P) (PP P),ddAt .x28 MB 1 (EP P),addAt (PP P) (EP P),
      P.ceLAt (PP P) P.dv (slotReg kC) (co+32*P.du*P.k)] s
      (fun t => VInvW P L s₀ kC co mE mB v rv mv P.k P.k t ∧
        bytesAt t.mem (kA s₀ (L.slot kC)+BitVec.ofNat 64 (co+32*P.du*P.k)) (32*P.dv)=
          compressEncode P.dv (vPoly P T rv mv)) := by
  have hw := hp.wf
  refine WPs.cons (WP.mono (invW_ok hp (po_TP hw) e₀.kb t₀.1 ht) fun s₁ ⟨kb₁, f₁, t₁, x₁⟩ => ?_)
  have e₁ := e₀.frame_far hp kb₁ x₁ f₁ (far_mul hp A (Nat.le_refl _) (Nat.le_refl _) (by lom) (by lom))
  rw [t₀.2] at t₁
  refine WPs.cons (WP.mono (valid hp (N := 2 * P.k) (by lom) (po_EP hw) e₁.kb e₁.r)
    fun s₂ ⟨kb₂, f₂, p₂, x₂⟩ => ?_)
  have e₂ := e₁.frame_far hp kb₂ x₂ f₂ (far_pcW hp A (Nat.le_refl _) (Nat.le_refl _) (by lom) (by lom))
  have fTP : ∀ r ∈ pcW L s₀ (EP P), (polyRegion (sA L s₀ (TP P))).Disjoint r := fun r hr => by
    rcases mem6 hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact sdisj hp (po_TP hw).le (by lom) (by lom)
    · exact sdisj hp (po_TP hw).le (by lom) (by lom)
    · exact below_R hp hp.scb (hp.fs (po_TP hw).le)
    · exact sdisj hp (po_TP hw).le (by lom) (by lom)
    · exact sdisj hp (po_TP hw).le (by lom) (by lom)
    · exact papart hp (po_TP hw) (po_EP hw) (by lom)
  have t₂ : PolyIsW 16 s₂.mem _ _ := polyIsW_frame_poly (w16 := true) f₂ fTP t₁
  refine WPs.cons (WP.mono (addW_read_ok hp (po_TP hw) (by lom) (.inr (by lom)) e₂.kb t₂.1 p₂.1)
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

theorem v_restW {prf : Nat→Nat→Prog isa} (valid : PrfValidW P L prf) {s₀ s : State} (hp : Pre P L s₀)
    (hc : Calls P) {kE eo kC co : Nat} (A : EncArgs P L kE eo kC co)
    {mE mB : Mem} {v : BitVec 64} {rv mv : List Byte} {T : Nat → Poly}
    (hT : ∀j<P.k, decode12 (bytesAt s₀.mem (kA s₀ (L.slot kE)+BitVec.ofNat 64 (eo+384*j)) 384)=T j)
    (htr : Optimized.TransformTables s)
    (h : VInvW P L s₀ kC co mE mB v rv mv P.k P.k s)
    (ht : Dot.GammaArtifact s.mem (s.syms "VG_MLKEM_GAMMA"))
    (hcT : Covers [⟨s.syms "VG_MLKEM_GAMMA",512⟩] (s.rd++s.wr))
    (ha : ∀r∈encW P L s₀ kC co, (⟨s.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint r) :
    WP isa (Kem16.vRest prf P (slotReg kE) eo .x28 MB (slotReg kC) co) s
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
  exact v_tailW valid hp hc A vu tru pu

end VG.Proof.MlKem.AArch64.Kem
