import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedMasks
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedInitialization
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedMaskVector
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.MaskPairLoop

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc seqR)
open VG.Proof.MlDsa.Sign
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.AArch64.Optimized

structure PositiveIL (p : Params) (S : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  k : PositiveIK p S σ s
  kap : s.mem.readW (pa s (sc oKAP)) 64=BitVec.ofNat 64 (p.ℓ*t)
  cnt : s.mem.readW (pa s (sc oCNT)) 64=BitVec.ofNat 64 (814-t)
  t_lt : t<814
  rej : RejT p σ t

theorem PositiveIL.st {p : Params} {S : Nat} {σ s : State} {t : Nat}
    (h : PositiveIL p S σ t s) : St p S σ s := h.k.d.im.st

theorem PositiveIL.step {p : Params} {S : Nat} {σ s u : State} {t : Nat}
    (h : PositiveIL p S σ t s) {ws : List (Ptr × Nat)}
    (hP : PPostB S s u ws) (hy : u.syms=s.syms) (hc : ilChk p ws=true)
    (hw : ∀w∈ws,inB (sgW p) w.1 w.2=true) : PositiveIL p S σ t u := by
  simp only [ilChk,ikChk,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨hd,hr⟩,hk⟩,hn⟩ := hc
  have L := h.st.lay
  exact ⟨⟨h.k.d.step hP hy hd hw,(L.keepBytes hP hr).trans h.k.rpp⟩,
    (L.keepW hP hk).trans h.kap,(L.keepW hP hn).trans h.cnt,h.t_lt,h.rej⟩

structure PositiveICm (p : Params) (S : Nat) (σ : State) (t r : Nat) (s : State) : Prop where
  l : PositiveIL p S σ t s
  y : Fam s (yBase p) r (Yv p σ (p.ℓ*t))
  yh : PosFam s (yhBase p) r (YHv p σ (p.ℓ*t))

def positiveIcmChk (p : Params) (ws : List (Ptr × Nat)) (r : Nat) : Bool :=
  icmChk p ws r && ws.all (fun w => inB (sgW p) w.1 w.2)

theorem PositiveICm.step {p : Params} {S : Nat} {σ s u : State} {t r : Nat}
    (h : PositiveICm p S σ t r s) {ws : List (Ptr × Nat)}
    (hP : PPostB S s u ws) (hy : u.syms=s.syms) (hc : positiveIcmChk p ws r=true) :
    PositiveICm p S σ t r u := by
  simp only [positiveIcmChk,icmChk,Bool.and_eq_true,List.all_eq_true] at hc
  obtain ⟨⟨⟨hl,hyc⟩,hyt⟩,hw⟩ := hc
  exact ⟨h.l.step hP hy hl hw,h.y.keep h.l.st.lay hP hyc,h.yh.keep h.l.st.lay hP hyt⟩

def positivePairSeedChk (p : Params) (r j : Nat) : Bool :=
  inB (sgB p) (sc oMS) 32 && inB (sgW p) (sc (oMP+66*j)) 32 &&
  sepB (sgR p) (sgW p) (sc oMS) 32 (sc (oMP+66*j)) 32 &&
  positiveIcmChk p [(sc (oMP+66*j),32)] r &&
  inB (sgB p) (sc (oMS+32)) 32 && inB (sgW p) (sc (oMP+66*j+32)) 32 &&
  sepB (sgR p) (sgW p) (sc (oMS+32)) 32 (sc (oMP+66*j+32)) 32 &&
  positiveIcmChk p [(sc (oMP+66*j+32),32)] r &&
  keepB (sgR p) (sgW p) [(sc (oMP+66*j+32),32)] (sc (oMP+66*j)) 32 &&
  inB (sgB p) (sc oKAP) 8 && inB (sgW p) (sc (oMP+66*j+64)) 2 &&
  positiveIcmChk p [(sc (oMP+66*j+64),2)] r &&
  keepB (sgR p) (sgW p) [(sc (oMP+66*j+64),2)] (sc (oMP+66*j)) 64 &&
  decide (p.ℓ*813+r+j<2^16) && decide (r+j<4096) && decide (j<2)

/-- Two word-oriented copies and two nonce stores prepare exactly the
standard 66-byte seed, preserving the earlier masks and signing state. -/
theorem positivePairSeed_ok {p : Params} {D : Nat} {σ s : State} {t r j : Nat}
    (hc : positivePairSeedChk p r j=true) (h : PositiveICm p D σ t r s) :
    WP isa (maskPairSeed r j) s fun u => PositiveICm p D σ t r u ∧
      PPostB D s u (pairSeedWrites j) ∧
      bytesAt u.mem (pa u (sc (oMP+66*j))) 66=
        rppOf p σ++integerToBytes (p.ℓ*t+(r+j)) 2 := by
  simp only [positivePairSeedChk,Bool.and_eq_true,and_assoc,decide_eq_true_eq] at hc
  obtain ⟨cr0,cw0,cs0,ci0,cr1,cw1,cs1,ci1,ck1,ck,cwn,cin,ckn,hx,hr,hj⟩ := hc
  unfold maskPairSeed
  refine WP.seq (WP.mono_syms (maskSeedHalf_ok h.l.st.lay (by decide) (by decide) cr0 cw0 cs0)
    fun a ⟨ha,_,hb0⟩ hya => ?_)
  have hA := h.step ha hya ci0
  have b0 : bytesAt a.mem (pa a (sc (oMP+66*j))) 32=(rppOf p σ).take 32 := by
    rw [ha.pa (by simp [keptRegs]),hb0,← VG.Proof.MlKem.bytesAt_take _ _ (by decide : 32≤64),h.l.k.rpp]
  refine WP.seq (WP.mono_syms (maskSeedHalf_ok hA.l.st.lay (by decide) (by decide) cr1 cw1 cs1)
    fun b ⟨hb,_,hb1⟩ hyb => ?_)
  have hB := hA.step hb hyb ci1
  have b1 : bytesAt b.mem (pa b (sc (oMP+66*j+32))) 32=(rppOf p σ).drop 32 := by
    rw [hb.pa (by simp [keptRegs]),hb1,← pa_sc_add]
    change bytesAt a.mem (pa a (sc oMS)+BitVec.ofNat 64 32) (64-32)=_
    rw [← VG.Proof.MlKem.bytesAt_drop _ _ (by decide : 32≤64),hA.l.k.rpp]
  have b64 : bytesAt b.mem (pa b (sc (oMP+66*j))) 64=rppOf p σ := by
    rw [show 64=32+32 from rfl,VG.Proof.MlKem.bytesAt_add,pa_sc_add,
      hA.l.st.lay.keepBytes hb ck1,b0,b1,List.take_append_drop]
  have hx' : p.ℓ*t+(r+j)<2^16 := by
    have := Nat.mul_le_mul_left p.ℓ (show t≤813 by have := h.l.t_lt; omega)
    omega
  refine WP.mono_syms (maskPairNonce_okB hB.l.st.lay hj hr hx' ck cwn hB.l.kap)
    fun u ⟨hu,_,hbn⟩ hyu => ?_
  have hab := PPostB.trans ha hb (ws := [(sc (oMP+66*j),32),(sc (oMP+66*j+32),32)])
    (by simp [sc,keptRegs]) (by simp) (by simp)
  refine ⟨hB.step hu hyu cin,?_,?_⟩
  · exact PPostB.trans hab hu (ws := pairSeedWrites j)
      (by simp [sc,keptRegs]) (by simp [pairSeedWrites]) (by simp [pairSeedWrites])
  · rw [VG.Proof.MlKem.bytesAt_add _ _ 64 2,hB.l.st.lay.keepBytes hu ckn,b64,
      pa_sc_add,hu.pa (by simp [keptRegs]),hbn]


def positiveFinishChk (p : Params) (n r : Nat) : Bool :=
  optimizedMaskChk p r && positiveIcmChk p [(yhP p r,1024)] r &&
    famChk (sgR p) (sgW p) [(yhP p r,1024)] (yBase p) n

theorem positiveFinish_ok {p : Params} {S : Nat} {σ s : State} {t n r : Nat}
    (hr : r<n) (hc : positiveFinishChk p n r=true) (h : PositiveICm p S σ t r s)
    (hy : Fam s (yBase p) n (Yv p σ (p.ℓ*t))) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.maskFinish p r) s fun u =>
      PositiveICm p S σ t (r+1) u ∧ Fam u (yBase p) n (Yv p σ (p.ℓ*t)) := by
  simp only [positiveFinishChk,optimizedMaskChk,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨ho,hi⟩,hw⟩,hd⟩,_⟩,_⟩,hc⟩,hykeep⟩ := hc
  have hf : PolyIs s.mem (pa s (yP p r)) (Yv p σ (p.ℓ*t) r) := hy r hr
  have ht : ForwardRoots s (pa s (yhP p r)) :=
    ⟨h.l.k.d.roots.nttTableAt (h.l.st.lay.inW hw),h.l.k.d.roots.forward.readable⟩
  refine WP.mono_syms (positiveNttOutAt_layout h.l.st.lay ho hi hw hd ht hf.1)
    fun u ⟨hu,_,hqu⟩ hsym => ?_
  have H := h.step hu hsym hc
  have hyu := hy.keep h.l.st.lay hu hykeep
  refine ⟨⟨H.l,fun j hj => hyu j (by omega),H.yh.snoc ?_⟩,hyu⟩
  change PosPolyIs u.mem (pa u (yhP p r)) _
  rw [hu.pa (h.l.st.lay.ptrBs ho)]
  rw [hf.2] at hqu
  exact hqu

def positivePairStepChk (p : Params) (r : Nat) : Bool :=
  positivePairSeedChk p r 0 && positivePairSeedChk p r 1 &&
  keepB (sgR p) (sgW p) (pairSeedWrites 1) (sc oMP) 66 &&
  maskPairChk (sgR p) (sgW p) (sc oMP) (yP p r) (yP p (r+1)) (sc (oR4 p)) &&
  positiveIcmChk p [(yP p r,1024),(yP p (r+1),1024),(sc (oR4 p),8192)] r &&
  positiveFinishChk p (r+2) r && positiveFinishChk p (r+2) (r+1) &&
  decide (p.γ₁=2^17 ∨ p.γ₁=2^19)

/-- Paired expansion advances the same canonical and transformed mask
invariants by two, with the original per-polynomial seeds. -/
theorem positivePairR_ok {D : Nat}
    {nm : String} {cd : Prog isa} (C : CalleeOk D cd (expandMaskPairContract AArch64.abi D))
    {p : Params} {σ s : State} {t r : Nat} (hc : positivePairStepChk p r=true)
    (h : PositiveICm p D σ t r s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.maskPairR p nm cd r) s (PositiveICm p D σ t (r+2)) := by
  simp only [positivePairStepChk,Bool.and_eq_true,and_assoc,decide_eq_true_eq] at hc
  obtain ⟨cs0,cs1,ck,cm,ci,cf0,cf1,hg⟩ := hc
  unfold Impl.MlDsa.AArch64.Sign.Optimized.maskPairR
  refine WP.seq (WP.mono (positivePairSeed_ok cs0 h) fun a ⟨hA,_,ha⟩ => ?_)
  refine WP.seq (WP.mono (positivePairSeed_ok cs1 hA) fun b ⟨hB,hb,hseed1⟩ => ?_)
  have hseed0 : bytesAt b.mem (pa b (sc oMP)) 66=
      rppOf p σ++integerToBytes (p.ℓ*t+r) 2 := by
    have hkeep := hA.l.st.lay.keepBytes hb ck
    simp only [Nat.mul_zero,Nat.add_zero] at ha
    rw [hkeep]
    exact ha
  have hseed1' : bytesAt b.mem (pa b (sc oMP)+66) 66=
      rppOf p σ++integerToBytes (p.ℓ*t+(r+1)) 2 := by
    change bytesAt b.mem (pa b (sc (oMP+66))) 66=_ at hseed1
    rw [← pa_sc_add] at hseed1
    exact hseed1
  refine WP.seq (WP.mono_syms (maskPairAt_ok hB.l.st.lay.s64 C hB.l.st.lay cm hg)
    fun c ⟨hcP,_,hy0,hy1⟩ hsy => ?_)
  rw [hseed0] at hy0
  rw [hseed1'] at hy1
  have hC := hB.step hcP hsy ci
  have hy : Fam c (yBase p) (r+2) (Yv p σ (p.ℓ*t)) := by
    refine Fam.snoc (Fam.snoc hC.y ?_) ?_
    · show PolyIs _ _ _
      rw [hcP.pa (pS_bases _)]
      exact hy0
    · show PolyIs _ _ _
      rw [hcP.pa (pS_bases _)]
      exact hy1
  refine WP.seq (WP.mono (positiveFinish_ok (by omega) cf0 hC hy) fun d ⟨hD,hyD⟩ => ?_)
  exact WP.mono (positiveFinish_ok (by omega) cf1 hD hyD) fun _ hu => hu.1


def positiveMaskChk (p : Params) (r : Nat) : Bool :=
  positiveIcmChk p [(sc (oMS+64),2)] r && inB (sgB p) (sc oKAP) 8 &&
  inB (sgW p) (sc (oMS+64)) 2 && maskChkS (sgR p) (sgW p) (yP p r) &&
  positiveIcmChk p [(yP p r,1024),(sc oPS,2048)] r && positiveFinishChk p (r+1) r &&
  decide (p.ℓ*813+r<2^16) && decide (r<4096) && decide (p.γ₁=2^17 ∨ p.γ₁=2^19)

theorem positiveMaskR_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    {σ s : State} {t r : Nat} (hc : positiveMaskChk p r=true) (h : PositiveICm p S σ t r s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.maskR P p r) s (PositiveICm p S σ t (r+1)) := by
  simp only [positiveMaskChk,Bool.and_eq_true,and_assoc,decide_eq_true_eq] at hc
  obtain ⟨c1,k1,w1,cm,c2,cf,hx,hr,hγ⟩ := hc
  have ht := h.l.t_lt
  have hx' : p.ℓ*t+r<2^16 := by
    have := Nat.mul_le_mul_left p.ℓ (show t≤813 by omega); omega
  unfold Impl.MlDsa.AArch64.Sign.Optimized.maskR
  refine WP.seq (WP.mono_syms (setKappa_okB h.l.st.lay hr hx' k1 w1 h.l.kap)
    fun s1 ⟨hP1,_,hb1⟩ hy1 => ?_)
  have I1 := h.step hP1 hy1 c1
  have hms : bytesAt s1.mem (pa s1 (sc oMS)) 66=rppOf p σ++integerToBytes (p.ℓ*t+r) 2 := by
    rw [VG.Proof.MlKem.bytesAt_add _ _ 64 2,I1.l.k.rpp,pa_sc_add,hP1.pa (by decide),hb1]
  refine WP.seq (WP.mono_syms (maskAt_ok hP I1.l.st.lay hγ cm)
    fun s2 ⟨hP2,_,hq2⟩ hy2 => ?_)
  rw [hms] at hq2
  have I2 := I1.step hP2 hy2 c2
  have hy : Fam s2 (yBase p) (r+1) (Yv p σ (p.ℓ*t)) :=
    I2.y.snoc (by
      show PolyIs _ _ _
      rw [hP2.pa (pS_bases _)]; exact hq2)
  exact WP.mono (positiveFinish_ok (by omega) cf I2 hy) fun _ hu => hu.1

def positiveMasksChk (p : Params) : Bool :=
  (List.range (p.ℓ/2)).all (fun j => positivePairStepChk p (2*j)) &&
  (List.range p.ℓ).all (positiveMaskChk p)

theorem positiveMasksChk_ok {p : Params} (hp : Ok3 p) : positiveMasksChk p=true := by
  rcases hp with rfl | rfl | rfl <;> decide +kernel

theorem positiveMasksPaired_ok {P : Prims} {S : Nat} (hP : PrimsOk P S)
    {nm : String} {cd : Prog isa} (C : CalleeOk S cd (expandMaskPairContract AArch64.abi S))
    {p : Params} {σ s : State} {t : Nat} (hc : positiveMasksChk p=true)
    (h : PositiveIL p S σ t s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.masksPaired P p nm cd) s (PositiveICm p S σ t p.ℓ) := by
  simp only [positiveMasksChk,Bool.and_eq_true,List.all_eq_true,List.mem_range] at hc
  unfold Impl.MlDsa.AArch64.Sign.Optimized.masksPaired
  refine WP.seq (WP.mono (seqR_ok (I:=fun j => PositiveICm p S σ t (2*j)) (p.ℓ/2) 0
    (fun j _ hj u hu => ?_) s ⟨h,fun _ h => by omega,fun _ h => by omega⟩) fun a ha => ?_)
  · simpa only [Nat.mul_add,Nat.mul_one] using positivePairR_ok C (hc.1 j (by omega)) hu
  · have he : 2*(p.ℓ/2)+p.ℓ%2=p.ℓ := by omega
    rw [Nat.zero_add] at ha
    have hw := seqR_ok (I:=fun r => PositiveICm p S σ t r) (p.ℓ%2) (2*(p.ℓ/2))
      (fun r _ hr u hu => positiveMaskR_ok hP (hc.2 r (by omega)) hu) a ha
    simpa only [he] using hw

theorem positiveMasks_ok {P : Prims} {S : Nat} (hP : PrimsOk P S)
    {p : Params} {σ s : State} {t : Nat} (hc : positiveMasksChk p=true) (h : PositiveIL p S σ t s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.masks P p) s (PositiveICm p S σ t p.ℓ) := by
  unfold Impl.MlDsa.AArch64.Sign.Optimized.masks
  split
  · exact positiveMasksPaired_ok hP hP.expandMaskPair hc h
  · simp only [positiveMasksChk,Bool.and_eq_true,List.all_eq_true,List.mem_range] at hc
    simpa only [Nat.zero_add] using seqR_ok (I:=fun r => PositiveICm p S σ t r) p.ℓ 0
      (fun r _ hr _ hh => positiveMaskR_ok hP (hc.2 r (by omega)) hh) s
      ⟨h,fun _ h => by omega,fun _ h => by omega⟩

end VG.Proof.MlDsa.AArch64.Sign
