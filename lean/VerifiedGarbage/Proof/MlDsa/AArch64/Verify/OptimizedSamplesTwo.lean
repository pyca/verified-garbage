import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedSamplesFour
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedCallTwo

namespace VG.Proof.MlDsa.AArch64.Verify.OptimizedSamples
open VG.Impl.MlDsa.AArch64.Call
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa (Params Reduced polyAt coeffAt poly4 seed4 Bounds rejNTTPoly minBounds)
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.KeyGen (masked_one masked_zero)

open VG.Proof.MlDsa.AArch64.KeyGen.Optimized

theorem vslot2_ok {p : Params} (hF : VFacts p) {S : Nat} {σ : State} (hp : vPre p S σ)
    {e j : Nat} (he : e+2 ≤ p.k*p.ℓ) (hj : j < 2) {s : State} (h : VS p σ e j s) :
    WP isa (seedSlot4 p e j) s (VS p σ e (j+1)) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  have L := h.va.vz.vc.lay hF hp
  unfold seedSlot4
  refine WP.seq (WP.mono (copySeed4_generic L (by vlayd) (by vlayd) (by vlayd)) fun s1 ⟨hP1,hk1,hb1⟩ => ?_)
  have h1 := h.va.keep hF hp hP1 (by vachk hF) (hk1.get .x24)
  have L1 := h1.vz.vc.lay hF hp
  unfold setSR
  refine WP.mono (vsetTwo_ok L1 (o := oSA4+34*j+32) (a := (e+j)%p.ℓ) (b := (e+j)/p.ℓ)
    (by dsimp only [oSA4]; omega) (by vlayd) (by vlayd)) fun t ⟨hP2,hk2,hb2⟩ => ?_
  refine ⟨h1.keep hF hp hP2 (by vachk hF) (hk2.get .x24),fun k hk => ?_⟩
  by_cases heq : k = j
  · subst k
    rw [bytes34,L1.keepBytes hP2 (by vlayd),sc_pa hP2,sc_pa hP1,hb1,h.va.rho,
      sc_add,← sc_pa hP1,hb2,seedOf,Proof.MlDsa.Verify.aSeed,integerToBytes_one,integerToBytes_one,List.append_assoc]
    rfl
  · rw [L1.keepBytes hP2 (by vlayd),L.keepBytes hP1 (by vlayd)]
    exact h.done k (by omega)

theorem vslot2_piece {p : Params} (hF : VFacts p) {S e j : Nat} (he : e+2 ≤ p.k*p.ℓ) (hj : j < 2) :
    VPiece p S (VS p · e j) (VS p · e (j+1)) (seedSlot4 p e j) :=
  ⟨fun _ _ hp h => vslot2_ok hF hp he hj h,
    vrel_of (Q := VTwo p S) (taintRel [.x28] (fun _ _ h => VTwo.x28 h) (slot_taint p e (by omega)))
      fun _ _ _ _ hp hp' hq h h' => vc_two hF hp hp' hq h.va.vz.vc h'.va.vz.vc⟩

theorem vseed2_eq {p : Params} {σ : State} {e : Nat} {s : State} (h : VS p σ e 2 s) {k : Nat} (hk : k < 2) :
    seed4 s.mem (pa s (sc oSA4)) k = seedOf p σ (e+k) := by
  unfold seed4
  rw [show pa s (sc oSA4)+BitVec.ofNat 64 (34*k) = pa s (sc (oSA4+34*k)) from sc_add _ _ _]
  exact h.done k hk

theorem vcall2_ok {S : Nat} (hS : S<2^64) {cd : Prog isa} {nm : String}
    (C : CalleeOk S cd (VG.Spec.MlDsa.rejNTT2Contract AArch64.abi S)) {p : Params} (hF : VFacts p)
    {σ : State} (hp : vPre p S σ) {e : Nat} (he : e+2 ≤ p.k*p.ℓ) {s : State} (h : VS p σ (e) 2 s) :
    WP isa (.seq (callAt nm cd (rej2Args (sc oSA4) (aP e) (sc (oR4 p))))
      (.seq (.block and24) (VG.Impl.MlDsa.AArch64.Optimized.MatrixMask.code (aP (e)) 512))) s (VA p σ (e+2)) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  have L := h.va.vz.vc.lay hF hp
  refine WP.seq (WP.mono (rej2At_ok hS C L
    (seed := sc oSA4) (a := aP (e)) (ss := sc (oR4 p)) (by unfold rej2Chk; vlayd))
    fun s2 ⟨hP2,h24,hred,hout⟩ => ?_)
  have L2 := L.post hP2
  have hr01 : (s2.gpr .x0).setWidth 32 = 0 ∨ (s2.gpr .x0).setWidth 32 = 1 := by
    rcases hout with ⟨h1,_⟩ | ⟨h0,_⟩; exacts [.inr h1,.inl h0]
  refine WP.seq (WP.mono (and24_ok s2) fun s20 ⟨h20,e24⟩ => ?_)
  have hP20 : PPostB S s2 s20 [] := postB_of_keep h20.keep (by decide) (by rw [h20.mem]; exact Frame.refl _ _)
  have L20 := L2.post hP20
  have hr20 : (s20.gpr .x0).setWidth 32 = 0 ∨ (s20.gpr .x0).setWidth 32 = 1 := by rw [h20.get .x0]; exact hr01
  refine WP.mono (VG.Proof.MlDsa.AArch64.Optimized.MatrixMask.mask_ok L20 (a := aP (e)) (N := 32) (by decide) (by decide) (by vlayd) (by vlayd) hr20) fun s3 ⟨hP3,k3,hco⟩ => ?_
  have hP23 := PPostB.app hP20 hP3 (sc_bases _ (by simp))
  have hP13 := PPostB.app hP2 hP23 (sc_bases _ (by simp))
  have e2 : pa s2 (aP (e)) = pa s (aP (e)) := sc_pa hP2 _
  have e20 : pa s20 (aP (e)) = pa s2 (aP (e)) := sc_pa hP20 _
  rw [h20.get .x0,e20,e2,h20.mem] at hco
  have hco4 : ∀ k < 2,∀ i < 256,coeffAt s3.mem (poly4 (pa s (aP (e))) k) i =
      if (s2.gpr .x0).setWidth 32 = 1 then coeffAt s2.mem (poly4 (pa s (aP (e))) k) i else 0 :=
    fun k hk i hi => by rw [coeffAt_poly4,coeffAt_poly4]; exact hco _ (by omega)
  have e3 : ∀ k,pa s3 (aP (e+k)) = poly4 (pa s (aP (e))) k := fun k => by rw [pa_poly4,sc_pa hP13]
  obtain ⟨q,hq,h1,h0⟩ := h.va.ok
  have hA : ∀ e' < e,polyAt s3.mem (pa s3 (aP e')) = polyAt s.mem (pa s (aP e')) := fun e' he' => L.keepPolyAt hP13 (by vlay)
  refine ⟨h.va.vz.keep hF hp hP13 (by vzchk hF),h.va.nok,by rw [L.keepBytes hP13 (by vlayd)]; exact h.va.rho,
    fun e' he' => ?_,q && ((s2.gpr .x0).setWidth 32 == 1),?_,fun hq' e' he' => ?_,fun hq' => ?_⟩
  · by_cases hlt : e' < e
    · exact L.keepRed hP13 (by vlay) (h.va.red e' hlt)
    · obtain ⟨k,rfl⟩ : ∃ k,e'=e+k := ⟨e'-e,by omega⟩
      rw [e3]
      by_cases hret : (s2.gpr .x0).setWidth 32 = 1
      · exact (masked_one hret (hco4 k (by omega))).2 (hred hret k (by omega))
      · exact (masked_zero hret (hco4 k (by omega))).1
  · rw [k3.get .x24,e24,h24,hq,and_flag _ (Q := (s2.gpr .x0).setWidth 32 = 1)
      (by rcases hr01 with h | h <;> rw [h] <;> decide)]
    exact flag_congr (by simp)
  · simp only [Bool.and_eq_true,beq_iff_eq] at hq'
    by_cases hlt : e' < e
    · obtain ⟨b,hb⟩ := h1 hq'.1 e' hlt
      exact ⟨b,by rw [hb,hA e' hlt]⟩
    · obtain ⟨k,rfl⟩ : ∃ k,e'=e+k := ⟨e'-e,by omega⟩
      rcases hout with ⟨_,hb⟩ | ⟨hret,_⟩
      · obtain ⟨b,hb⟩ := hb k (by omega)
        exact ⟨b,by rw [e3,(masked_one hq'.2 (hco4 k (by omega))).1,← vseed2_eq h (by omega)]; exact hb⟩
      · rw [hq'.2] at hret; exact absurd hret (by decide)
  · cases hqq : q
    · obtain ⟨e',he',hn⟩ := h0 hqq; exact ⟨e',by omega,hn⟩
    · rw [hqq] at hq'
      simp only [Bool.true_and,beq_eq_false_iff_ne,ne_eq] at hq'
      rcases hout with ⟨hret,_⟩ | ⟨_,k,hk,hn⟩
      · exact absurd hret hq'
      · exact ⟨e+k,by omega,by rw [← vseed2_eq h hk]; exact hn⟩



end VG.Proof.MlDsa.AArch64.Verify.OptimizedSamples
