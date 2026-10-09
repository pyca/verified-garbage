import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseCCTBase
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.MaskPairLoop

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc)
open VG.Proof.MlDsa.Sign VG.Spec.MlDsa

private theorem half_taint (src dst : Nat) :
    (taint.check (AArch64.Taint.ofRegs bases) (.block (maskSeedHalf src dst)) (.block [])).isSome=true := by
  dsimp only [maskSeedHalf,VG.Impl.MlDsa.AArch64.Call.lea,VG.Impl.MlDsa.AArch64.Call.movV,Impl.MlKem.AArch64.copy32]
  repeat' split
  all_goals rfl

private theorem nonce_taint (r j : Nat) :
    (taint.check (AArch64.Taint.ofRegs bases) (.block (maskPairNonce r j)) (.block [])).isSome=true := by
  dsimp only [maskPairNonce]; rfl

private theorem seed_post {p : Params} {D : Nat} {r j : Nat} {s : State}
    (L : Lay D (sgR p) (sgW p) s) (hc : pairSeedChk p r j=true) :
    WP isa (maskPairSeed r j) s fun u => ∃ W,PostB D s u W := by
  simp only [pairSeedChk,Bool.and_eq_true,and_assoc,decide_eq_true_eq] at hc
  obtain ⟨cr0,cw0,cs0,_,cr1,cw1,cs1,_,_,ck,cwn,_,_,_,hr,hj⟩ := hc
  unfold maskPairSeed
  refine WP.seq (WP.mono (maskSeedHalf_ok L (by decide) (by decide) cr0 cw0 cs0) fun a ⟨ha,_,_⟩ => ?_)
  refine WP.seq (WP.mono (maskSeedHalf_ok (L.post ha) (by decide) (by decide) cr1 cw1 cs1) fun b ⟨hb,_,_⟩ => ?_)
  refine WP.mono (maskPairNonce_post ((L.post ha).post hb) hj hr ck cwn) fun u ⟨W,hu⟩ => ?_
  have hab := PostB.trans ha hb (W := _++_)
    (fun r hr => List.mem_append_left _ hr) (fun r hr => List.mem_append_right _ hr)
  exact ⟨_,PostB.trans hab hu (W := _++W)
    (fun r hr => List.mem_append_left _ hr) (fun r hr => List.mem_append_right _ hr)⟩

private theorem seed_tr {p : Params} {D : Nat} {r j : Nat} (hc : pairSeedChk p r j=true) :
    RelCT isa (LRel D (sgR p) (sgW p)) (maskPairSeed r j) fun _ _ => True := by
  simp only [pairSeedChk,Bool.and_eq_true,and_assoc,decide_eq_true_eq] at hc
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

private theorem finish_tr {P : Prims} {D : Nat} (hP : PrimsOk P D)
    {p : Params} {n r : Nat} (hc : maskFinishChk p n r=true) :
    RelCT isa (fun x y => LRel D (sgR p) (sgW p) x y ∧
      Reduced x.mem (pa x (yP p r)) ∧ Reduced y.mem (pa y (yP p r)))
      (maskFinish P p r) fun _ _ => True := by
  simp only [maskFinishChk,Bool.and_eq_true,and_assoc] at hc
  obtain ⟨cc,_,_,ci,_,_⟩ := hc
  unfold maskFinish
  exact seqL (J := fun s => Reduced s.mem (pa s (yhP p r)))
    (copy_tr (.inl rfl) rfl fun _ _ h => h.1)
    (fun x L hy => WP.mono (copy_ok L cc) fun u ⟨hu,_,hb⟩ =>
      ⟨⟨_,hu⟩,by rw [hu.pa (pS_bases _)]; exact reduced_congr₂ (bytes_of_bytesAt hb) hy⟩)
    (ipAt_tr (t := ntt) hP.ntt ci)

private theorem finish_post {P : Prims} {D : Nat} (hP : PrimsOk P D)
    {p : Params} {n r j : Nat} {s : State} (L : Lay D (sgR p) (sgW p) s)
    (hc : maskFinishChk p n r=true) (hj : j<n)
    (hr : Reduced s.mem (pa s (yP p r))) (hkeep : Reduced s.mem (pa s (yP p j))) :
    WP isa (maskFinish P p r) s fun u => (∃ W,PostB D s u W) ∧
      Reduced u.mem (pa u (yP p j)) := by
  simp only [maskFinishChk,Bool.and_eq_true,and_assoc] at hc
  obtain ⟨cc,_,fy1,ci,_,fy2⟩ := hc
  unfold maskFinish
  refine WP.seq (WP.mono (copy_ok L cc) fun a ⟨ha,_,hb⟩ => ?_)
  have hy : Reduced a.mem (pa a (yhP p r)) := by
    rw [ha.pa (pS_bases _)]; exact reduced_congr₂ (bytes_of_bytesAt hb) hr
  refine WP.mono (ipAt_ok (t := ntt) hP.ntt (L.post ha) ci hy) fun u ⟨hu,_,_⟩ => ?_
  exact ⟨⟨_,PostB.trans ha hu (W := _++_)
    (fun r hr => List.mem_append_left _ hr) (fun r hr => List.mem_append_right _ hr)⟩,
    (L.post ha).keepRed hu (famChk_one fy2 hj) (L.keepRed ha (famChk_one fy1 hj) hkeep)⟩

/-- The paired mask phase has the same pointer-only timing policy as two
ordinary mask expansions. -/
theorem maskPairR_trL {P : Prims} {D : Nat} (hP : PrimsOk P D)
    {nm : String} {cd : Prog isa} (C : CalleeOk D cd (expandMaskPairContract AArch64.abi D))
    {p : Params} {r : Nat} (hc : maskPairStepChk p r=true) :
    RelCT isa (LRel D (sgR p) (sgW p)) (maskPairR P p nm cd r) fun _ _ => True := by
  simp only [maskPairStepChk,Bool.and_eq_true,and_assoc,decide_eq_true_eq] at hc
  obtain ⟨cs0,cs1,_,cm,_,cf0,cf1,hg⟩ := hc
  have hcall : RelCT isa (LRel D (sgR p) (sgW p))
      (VG.Impl.MlDsa.AArch64.Call.callAt nm cd (maskPairArgs (sc oMP) p.γ₁ (yP p r) (yP p (r+1)) (sc (oR4 p))))
      (fun _ _ => True) := fun x y tr₁ tr₂ u v h e₁ e₂ =>
    maskPairAt_tr C h.ok cm hg (fun _ _ h => ⟨h.lx,h.ly,h.same⟩) x y tr₁ tr₂ u v h e₁ e₂
  unfold maskPairR
  refine RelCT.mono (seqL (p := p) (I := fun _ => True) (J := fun _ => True)
    (RelCT.mono (seed_tr cs0) (fun _ _ h => h.1) (fun _ _ h => h))
    (fun _ L _ => WP.mono (seed_post L cs0) fun _ h => ⟨h,trivial⟩)
    (seqL (J := fun _ => True)
      (RelCT.mono (seed_tr cs1) (fun _ _ h => h.1) (fun _ _ h => h))
      (fun _ L _ => WP.mono (seed_post L cs1) fun _ h => ⟨h,trivial⟩)
      (seqL (J := fun s => Reduced s.mem (pa s (yP p r)) ∧ Reduced s.mem (pa s (yP p (r+1))))
        (RelCT.mono hcall (fun _ _ h => h.1) (fun _ _ h => h))
        (fun _ L _ => WP.mono (maskPairAt_ok L.s64 C L cm hg) fun u ⟨hu,_,ha,hb⟩ =>
          ⟨⟨_,hu⟩,by rw [hu.pa (pS_bases _)]; exact ha.1,by rw [hu.pa (pS_bases _)]; exact hb.1⟩)
        (seqL (J := fun s => Reduced s.mem (pa s (yP p (r+1))))
          (trL_mono (finish_tr hP cf0) (fun _ h => h.1))
          (fun _ L h => finish_post hP L cf0 (by omega) h.1 h.2)
          (finish_tr hP cf1)))))
    (fun _ _ h => ⟨h,trivial,trivial⟩) (fun _ _ h => h)

theorem masksPaired_tr {P : Prims} {D : Nat} (hP : PrimsOk P D)
    {nm : String} {cd : Prog isa} (C : CalleeOk D cd (expandMaskPairContract AArch64.abi D))
    {p : Params} (hc : masksPairChk p=true) {E : State → State → Prop} {t : Nat} :
    RelCT isa (RS p D E fun σ s => IL p D σ t s) (masksPaired P p nm cd)
      (RS p D E fun σ s => ICm p D σ t p.ℓ s) := by
  simp only [masksPairChk,Bool.and_eq_true,List.all_eq_true,List.mem_range] at hc
  unfold masksPaired
  refine RelCT.seq (R := RS p D E fun σ s => ICm p D σ t (2*(p.ℓ/2)) s) ?_ ?_
  · refine RelCT.mono (seqR_tr (Q := fun j => RS p D E fun σ s => ICm p D σ t (2*j) s)
      (p.ℓ/2) 0 fun j _ hj => ?_)
      (fun x y h => h.mono (fun _ _ h => h) fun _ _ h => ⟨h,fun _ h => by omega,fun _ h => by omega⟩)
      (fun x y h => by simpa only [Nat.zero_add] using h)
    have hh : RelCT isa (RS p D E fun σ s => ICm p D σ t (2*j) s)
        (maskPairR P p nm cd (2*j)) (RS p D E fun σ s => ICm p D σ t (2*j+2) s) :=
      liftT (fun _ _ h => h.l.st)
      (fun _ _ _ h => maskPairR_ok hP C (hc.1 j (by omega)) h)
      (maskPairR_trL hP C (hc.1 j (by omega)))
    simpa only [Nat.mul_add,Nat.mul_one] using hh
  · have he : 2*(p.ℓ/2)+p.ℓ%2=p.ℓ := by omega
    have hh := seqR_tr (Q := fun r => RS p D E fun σ s => ICm p D σ t r s)
      (p.ℓ%2) (2*(p.ℓ/2)) fun r _ hr =>
        liftT (fun _ _ h => h.l.st) (fun _ _ _ h => maskR_ok hP (hc.2 r (by omega)) h)
          (maskR_trL hP (hc.2 r (by omega)))
    simpa only [he] using hh

theorem masks_tr {P : Prims} {D : Nat} (hP : PrimsOk P D)
    {p : Params} (hc : masksPairChk p=true) {E : State → State → Prop} {t : Nat} :
    RelCT isa (RS p D E fun σ s => IL p D σ t s) (masks P p)
      (RS p D E fun σ s => ICm p D σ t p.ℓ s) := by
  unfold masks
  split
  · exact masksPaired_tr hP hP.expandMaskPair hc
  · simp only [masksPairChk,Bool.and_eq_true,List.all_eq_true,List.mem_range] at hc
    refine RelCT.mono (seqR_tr (Q := fun r => RS p D E fun σ s => ICm p D σ t r s) p.ℓ 0
      fun r _ hr => liftT (fun _ _ h => h.l.st)
        (fun _ _ _ h => maskR_ok hP (hc.2 r (by omega)) h) (maskR_trL hP (hc.2 r (by omega))))
      (fun x y h => h.mono (fun _ _ h => h) fun _ _ h => ⟨h,fun _ h => by omega,fun _ h => by omega⟩)
      (fun x y h => by simpa only [Nat.zero_add] using h)

end VG.Proof.MlDsa.AArch64.Sign
