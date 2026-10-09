import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedMasks
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.MaskPairTiming

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc seqR)
open VG.Proof.MlDsa.Sign VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- The immutable forward-table address is public at the private optimized boundary. -/
def MaskRS (p : Params) (S : Nat) (E I : State → State → Prop) (x y : State) : Prop :=
  RS p S E I x y ∧ x.syms "VG_MLDSA_NTT_EXPANDED"=y.syms "VG_MLDSA_NTT_EXPANDED"

theorem MaskRS.mono {p : Params} {S : Nat} {E I J : State → State → Prop} {x y : State}
    (h : MaskRS p S E I x y) (hf : ∀σ s,I σ s → J σ s) : MaskRS p S E J x y :=
  ⟨h.1.mono (fun _ _ h => h) hf,h.2⟩

theorem liftMask {p : Params} {S : Nat} {E I J : State → State → Prop} {c : Prog isa}
    (hw : ∀σ s,(signK p S).pre σ → I σ s → WP isa c s (J σ))
    (ht : RelCT isa (MaskRS p S E I) c fun _ _ => True) :
    RelCT isa (MaskRS p S E I) c (MaskRS p S E J) := by
  intro x y tx ty u v h ex ey
  obtain ⟨htrace,_⟩ := ht _ _ _ _ _ _ h ex ey
  obtain ⟨⟨σ,τ,ps,pt,hpub,he,ix,iy⟩,hsym⟩ := h
  obtain ⟨_,u',eu,ju,hyu⟩ := WP.mono_syms (R := fun u => J σ u ∧ u.syms=x.syms) (hw σ x ps ix) (fun _ h hy => ⟨h,hy⟩)
  obtain ⟨_,v',ev,jv,hyv⟩ := WP.mono_syms (R := fun v => J τ v ∧ v.syms=y.syms) (hw τ y pt iy) (fun _ h hy => ⟨h,hy⟩)
  obtain ⟨_,rfl⟩ := Exec.det ex eu
  obtain ⟨_,rfl⟩ := Exec.det ey ev
  exact ⟨htrace,⟨σ,τ,ps,pt,hpub,he,ju,jv⟩,by rw [hyu,hyv]; exact hsym⟩

private theorem half_taint (src dst : Nat) :
    (taint.check (AArch64.Taint.ofRegs bases) (.block (maskSeedHalf src dst)) (.block [])).isSome=true := by
  dsimp only [maskSeedHalf,VG.Impl.MlDsa.AArch64.Call.lea,VG.Impl.MlDsa.AArch64.Call.movV,Impl.MlKem.AArch64.copy32]
  repeat' split
  all_goals rfl

private theorem nonce_taint (r j : Nat) :
    (taint.check (AArch64.Taint.ofRegs bases) (.block (maskPairNonce r j)) (.block [])).isSome=true := by
  dsimp only [maskPairNonce]; rfl

private theorem seed_tr {p : Params} {D : Nat} {r j : Nat} (hc : positivePairSeedChk p r j=true) :
    RelCT isa (LRel D (sgR p) (sgW p)) (maskPairSeed r j) fun _ _ => True := by
  simp only [positivePairSeedChk,Bool.and_eq_true,and_assoc,decide_eq_true_eq] at hc
  obtain ⟨cr0,cw0,cs0,_,cr1,cw1,cs1,_,_,_,_,_,_,_,_,_⟩ := hc
  unfold maskPairSeed
  refine RelCT.mono (seqL (p := p) (I := fun _ => True) (J := fun _ => True)
    (lrel_tr (fun _ _ h => h.1) (half_taint _ _))
    (fun _ L _ => WP.mono (maskSeedHalf_ok L (by decide) (by decide) cr0 cw0 cs0)
      fun _ ⟨h,_,_⟩ => ⟨⟨_,h⟩,trivial⟩)
    (seqL (J := fun _ => True)
      (lrel_tr (fun _ _ h => h.1) (half_taint _ _))
      (fun _ L _ => WP.mono (maskSeedHalf_ok L (by decide) (by decide) cr1 cw1 cs1)
        fun _ ⟨h,_,_⟩ => ⟨⟨_,h⟩,trivial⟩)
      (lrel_tr (fun _ _ h => h.1) (nonce_taint r j))))
    (fun _ _ h => ⟨h,trivial,trivial⟩) (fun _ _ h => h)

private theorem finish_tr {p : Params} {S : Nat} {E : State → State → Prop} {t n r : Nat}
    (hr : r<n) (hc : positiveFinishChk p n r=true) :
    RelCT isa (MaskRS p S E fun σ s => PositiveICm p S σ t r s ∧ Fam s (yBase p) n (Yv p σ (p.ℓ*t)))
      (Impl.MlDsa.AArch64.Sign.Optimized.maskFinish p r)
      (MaskRS p S E fun σ s => PositiveICm p S σ t (r+1) s ∧ Fam s (yBase p) n (Yv p σ (p.ℓ*t))) := by
  refine liftMask (fun _ _ _ h => positiveFinish_ok hr hc h.1 h.2) ?_
  apply optimizedMaskFinish_tr (S:=S) (by
    simp only [positiveFinishChk,Bool.and_eq_true] at hc; exact hc.1.1)
  intro x y h
  have L := h.1.lrel (fun _ _ h => h.1.l.st)
  obtain ⟨σ,τ,_,_,_,_,ix,iy⟩ := h.1
  exact ⟨⟨σ,ix.1.l.st,ix.1.l.k.d.roots⟩,⟨τ,iy.1.l.st,iy.1.l.k.d.roots⟩,
    (ix.2 r hr).1,(iy.2 r hr).1,L.regs .x28 (by decide),L.sp,h.2⟩

theorem positivePairR_tr {S : Nat} {nm : String} {cd : Prog isa}
    (C : CalleeOk S cd (expandMaskPairContract AArch64.abi S)) {p : Params} {r t : Nat}
    (hc : positivePairStepChk p r=true) {E : State → State → Prop} :
    RelCT isa (MaskRS p S E fun σ s => PositiveICm p S σ t r s)
      (Impl.MlDsa.AArch64.Sign.Optimized.maskPairR p nm cd r)
      (MaskRS p S E fun σ s => PositiveICm p S σ t (r+2) s) := by
  simp only [positivePairStepChk,Bool.and_eq_true,and_assoc,decide_eq_true_eq] at hc
  obtain ⟨cs0,cs1,ck,cm,ci,cf0,cf1,hg⟩ := hc
  let A σ s := PositiveICm p S σ t r s ∧
    bytesAt s.mem (pa s (sc oMP)) 66=rppOf p σ++integerToBytes (p.ℓ*t+r) 2
  let B σ s := A σ s ∧ bytesAt s.mem (pa s (sc oMP)+66) 66=
    rppOf p σ++integerToBytes (p.ℓ*t+(r+1)) 2
  let D σ s := PositiveICm p S σ t r s ∧ Fam s (yBase p) (r+2) (Yv p σ (p.ℓ*t))
  unfold Impl.MlDsa.AArch64.Sign.Optimized.maskPairR
  refine RelCT.seq (R:=MaskRS p S E A) (liftMask ?_ ?_) ?_
  · intro σ s _ h
    exact WP.mono (positivePairSeed_ok cs0 h) fun u ⟨hu,_,hb⟩ =>
      ⟨hu,by simpa only [Nat.mul_zero,Nat.add_zero] using hb⟩
  · exact RelCT.mono (seed_tr cs0) (fun _ _ h => h.1.lrel (fun _ _ h => h.l.st)) (fun _ _ h => h)
  refine RelCT.seq (R:=MaskRS p S E B) (liftMask ?_ ?_) ?_
  · intro σ s _ h
    refine WP.mono (positivePairSeed_ok cs1 h.1) fun u ⟨hu,hP,hb⟩ => ⟨⟨hu,?_⟩,?_⟩
    · rw [h.1.l.st.lay.keepBytes hP ck]; exact h.2
    · change bytesAt u.mem (pa u (sc (oMP+66))) 66=_ at hb
      rw [← pa_sc_add] at hb; exact hb
  · exact RelCT.mono (seed_tr cs1) (fun _ _ h => h.1.lrel (fun _ _ h => h.1.l.st)) (fun _ _ h => h)
  refine RelCT.seq (R:=MaskRS p S E D) (liftMask ?_ ?_) ?_
  · intro σ s _ h
    refine WP.mono_syms (maskPairAt_ok h.1.1.l.st.lay.s64 C h.1.1.l.st.lay cm hg)
      fun u ⟨hu,_,hy0,hy1⟩ hsym => ?_
    rw [h.1.2] at hy0
    rw [h.2] at hy1
    have H := h.1.1.step hu hsym ci
    refine ⟨H,H.y.snoc ?_ |>.snoc ?_⟩
    · show PolyIs _ _ _; rw [hu.pa (pS_bases _)]; exact hy0
    · show PolyIs _ _ _; rw [hu.pa (pS_bases _)]; exact hy1
  · intro x y tx ty u v h ex ey
    have L := h.1.lrel (fun _ _ h => h.1.1.l.st)
    exact maskPairAt_tr C L.ok cm hg (fun _ _ h => ⟨h.lx,h.ly,h.same⟩) _ _ _ _ _ _ L ex ey
  refine RelCT.seq (finish_tr (by omega) cf0) ?_
  exact RelCT.mono (finish_tr (by omega) cf1) (fun _ _ h => h)
    (fun _ _ h => h.mono (fun _ _ h => h.1))

theorem positiveMaskR_tr {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} {r t : Nat}
    (hc : positiveMaskChk p r=true) {E : State → State → Prop} :
    RelCT isa (MaskRS p S E fun σ s => PositiveICm p S σ t r s)
      (Impl.MlDsa.AArch64.Sign.Optimized.maskR P p r)
      (MaskRS p S E fun σ s => PositiveICm p S σ t (r+1) s) := by
  simp only [positiveMaskChk,Bool.and_eq_true,and_assoc,decide_eq_true_eq] at hc
  obtain ⟨c1,k1,w1,cm,c2,cf,hx,hr,hγ⟩ := hc
  let A σ s := PositiveICm p S σ t r s ∧
    bytesAt s.mem (pa s (sc oMS)) 66=rppOf p σ++integerToBytes (p.ℓ*t+r) 2
  let B σ s := PositiveICm p S σ t r s ∧ Fam s (yBase p) (r+1) (Yv p σ (p.ℓ*t))
  unfold Impl.MlDsa.AArch64.Sign.Optimized.maskR
  refine RelCT.seq (R:=MaskRS p S E A) (liftMask ?_ ?_) ?_
  · intro σ s _ h
    have hx' : p.ℓ*t+r<2^16 := by
      have := Nat.mul_le_mul_left p.ℓ (show t≤813 by have := h.l.t_lt; omega); omega
    refine WP.mono_syms (setKappa_okB h.l.st.lay hr hx' k1 w1 h.l.kap)
      fun u ⟨hu,_,hb⟩ hsym => ?_
    have H := h.step hu hsym c1
    refine ⟨H,?_⟩
    rw [VG.Proof.MlKem.bytesAt_add _ _ 64 2,H.l.k.rpp,pa_sc_add,hu.pa (by decide),hb]
  · exact lrel_tr (fun _ _ h => h.1.lrel (fun _ _ h => h.l.st)) (setKappa_taint r)
  refine RelCT.seq (R:=MaskRS p S E B) (liftMask ?_ ?_) ?_
  · intro σ s _ h
    refine WP.mono_syms (maskAt_ok hP h.1.l.st.lay hγ cm) fun u ⟨hu,_,hy⟩ hsym => ?_
    rw [h.2] at hy
    have H := h.1.step hu hsym c2
    refine ⟨H,H.y.snoc ?_⟩
    show PolyIs _ _ _; rw [hu.pa (pS_bases _)]; exact hy
  · exact RelCT.mono (maskAt_tr hP hγ cm) (fun _ _ h => h.1.lrel (fun _ _ h => h.1.l.st)) (fun _ _ h => h)
  exact RelCT.mono (finish_tr (by omega) cf) (fun _ _ h => h) (fun _ _ h => h.mono (fun _ _ h => h.1))

theorem positiveMasksPaired_tr {P : Prims} {S : Nat} (hP : PrimsOk P S)
    {nm : String} {cd : Prog isa} (C : CalleeOk S cd (expandMaskPairContract AArch64.abi S))
    {p : Params} (hc : positiveMasksChk p=true) {E : State → State → Prop} {t : Nat} :
    RelCT isa (MaskRS p S E fun σ s => PositiveIL p S σ t s)
      (Impl.MlDsa.AArch64.Sign.Optimized.masksPaired P p nm cd)
      (MaskRS p S E fun σ s => PositiveICm p S σ t p.ℓ s) := by
  simp only [positiveMasksChk,Bool.and_eq_true,List.all_eq_true,List.mem_range] at hc
  unfold Impl.MlDsa.AArch64.Sign.Optimized.masksPaired
  refine RelCT.seq (R:=MaskRS p S E fun σ s => PositiveICm p S σ t (2*(p.ℓ/2)) s) ?_ ?_
  · refine RelCT.mono (seqR_tr (Q:=fun j => MaskRS p S E fun σ s => PositiveICm p S σ t (2*j) s)
      (p.ℓ/2) 0 fun j _ hj => ?_)
      (fun _ _ h => h.mono (fun _ _ h => ⟨h,fun _ h => by omega,fun _ h => by omega⟩))
      (fun _ _ h => by simpa only [Nat.zero_add] using h)
    simpa only [Nat.mul_add,Nat.mul_one] using positivePairR_tr C (hc.1 j (by omega)) (t:=t) (E:=E)
  · have he : 2*(p.ℓ/2)+p.ℓ%2=p.ℓ := by omega
    have hh := seqR_tr (Q:=fun r => MaskRS p S E fun σ s => PositiveICm p S σ t r s)
      (p.ℓ%2) (2*(p.ℓ/2)) fun r _ hr => positiveMaskR_tr hP (hc.2 r (by omega))
    simpa only [he] using hh

theorem positiveMasks_tr {P : Prims} {S : Nat} (hP : PrimsOk P S)
    {p : Params} (hc : positiveMasksChk p=true) {E : State → State → Prop} {t : Nat} :
    RelCT isa (MaskRS p S E fun σ s => PositiveIL p S σ t s)
      (Impl.MlDsa.AArch64.Sign.Optimized.masks P p)
      (MaskRS p S E fun σ s => PositiveICm p S σ t p.ℓ s) := by
  unfold Impl.MlDsa.AArch64.Sign.Optimized.masks
  split
  · exact positiveMasksPaired_tr hP hP.expandMaskPair hc
  · simp only [positiveMasksChk,Bool.and_eq_true,List.all_eq_true,List.mem_range] at hc
    refine RelCT.mono (seqR_tr (Q:=fun r => MaskRS p S E fun σ s => PositiveICm p S σ t r s) p.ℓ 0
      fun r _ hr => positiveMaskR_tr hP (hc.2 r (by omega)))
      (fun _ _ h => h.mono (fun _ _ h => ⟨h,fun _ h => by omega,fun _ h => by omega⟩))
      (fun _ _ h => by simpa only [Nat.zero_add] using h)

end VG.Proof.MlDsa.AArch64.Sign
