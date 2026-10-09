import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Samp4
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MatrixMask
import VerifiedGarbage.Impl.MlDsa.AArch64.Verify.OptimizedSamples

namespace VG.Proof.MlDsa.AArch64.Verify.OptimizedSamples
open VG.Impl.MlDsa.AArch64.Call
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa (Params Reduced polyAt coeffAt poly4 seed4 Bounds rejNTTPoly minBounds)
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.KeyGen (masked_one masked_zero)

theorem vcall4_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p)
    {σ : State} (hp : vPre p S σ) {g : Nat} (hg : 4*g+4 ≤ p.k*p.ℓ) {s : State} (h : VS p σ (4*g) 4 s) :
    WP isa (.seq (rej4At P (sc (oR4 p)) (sc oSA4) (aP (4*g)))
      (.seq (.block and24) (VG.Impl.MlDsa.AArch64.Optimized.MatrixMask.code (aP (4*g)) 1024))) s (VA p σ (4*g+4)) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  have L := h.va.vz.vc.lay hF hp
  refine WP.seq (WP.mono (rej4At_ok hP.s64 hP.rej4 L
    (seed := sc oSA4) (a := aP (4*g)) (ss := sc (oR4 p)) (by unfold rej4Chk; vlay))
    fun s2 ⟨hP2,h24,hred,hout⟩ => ?_)
  have L2 := L.post hP2
  have hr01 : (s2.gpr .x0).setWidth 32 = 0 ∨ (s2.gpr .x0).setWidth 32 = 1 := by
    rcases hout with ⟨h1,_⟩ | ⟨h0,_⟩; exacts [.inr h1,.inl h0]
  refine WP.seq (WP.mono (and24_ok s2) fun s20 ⟨h20,e24⟩ => ?_)
  have hP20 : PPostB S s2 s20 [] := postB_of_keep h20.keep (by decide) (by rw [h20.mem]; exact Frame.refl _ _)
  have L20 := L2.post hP20
  have hr20 : (s20.gpr .x0).setWidth 32 = 0 ∨ (s20.gpr .x0).setWidth 32 = 1 := by rw [h20.get .x0]; exact hr01
  refine WP.mono (VG.Proof.MlDsa.AArch64.Optimized.MatrixMask.mask_ok L20 (a := aP (4*g)) (N := 64) (by decide) (by decide) (by vlay) (by vlay) hr20) fun s3 ⟨hP3,k3,hco⟩ => ?_
  have hP23 := PPostB.app hP20 hP3 (sc_bases _ (by simp))
  have hP13 := PPostB.app hP2 hP23 (sc_bases _ (by simp))
  have e2 : pa s2 (aP (4*g)) = pa s (aP (4*g)) := sc_pa hP2 _
  have e20 : pa s20 (aP (4*g)) = pa s2 (aP (4*g)) := sc_pa hP20 _
  rw [h20.get .x0,e20,e2,h20.mem] at hco
  have hco4 : ∀ k < 4,∀ i < 256,coeffAt s3.mem (poly4 (pa s (aP (4*g))) k) i =
      if (s2.gpr .x0).setWidth 32 = 1 then coeffAt s2.mem (poly4 (pa s (aP (4*g))) k) i else 0 :=
    fun k hk i hi => by rw [coeffAt_poly4,coeffAt_poly4]; exact hco _ (by omega)
  have e3 : ∀ k,pa s3 (aP (4*g+k)) = poly4 (pa s (aP (4*g))) k := fun k => by rw [pa_poly4,sc_pa hP13]
  obtain ⟨q,hq,h1,h0⟩ := h.va.ok
  have hA : ∀ e' < 4*g,polyAt s3.mem (pa s3 (aP e')) = polyAt s.mem (pa s (aP e')) := fun e' he' => L.keepPolyAt hP13 (by vlay)
  refine ⟨h.va.vz.keep hF hp hP13 (by vzchk hF),h.va.nok,by rw [L.keepBytes hP13 (by vlay)]; exact h.va.rho,
    fun e' he' => ?_,q && ((s2.gpr .x0).setWidth 32 == 1),?_,fun hq' e' he' => ?_,fun hq' => ?_⟩
  · by_cases hlt : e' < 4*g
    · exact L.keepRed hP13 (by vlay) (h.va.red e' hlt)
    · obtain ⟨k,rfl⟩ : ∃ k,e'=4*g+k := ⟨e'-4*g,by omega⟩
      rw [e3]
      by_cases hret : (s2.gpr .x0).setWidth 32 = 1
      · exact (masked_one hret (hco4 k (by omega))).2 (hred hret k (by omega))
      · exact (masked_zero hret (hco4 k (by omega))).1
  · rw [k3.get .x24,e24,h24,hq,and_flag _ (Q := (s2.gpr .x0).setWidth 32 = 1)
      (by rcases hr01 with h | h <;> rw [h] <;> decide)]
    exact flag_congr (by simp)
  · simp only [Bool.and_eq_true,beq_iff_eq] at hq'
    by_cases hlt : e' < 4*g
    · obtain ⟨b,hb⟩ := h1 hq'.1 e' hlt
      exact ⟨b,by rw [hb,hA e' hlt]⟩
    · obtain ⟨k,rfl⟩ : ∃ k,e'=4*g+k := ⟨e'-4*g,by omega⟩
      rcases hout with ⟨_,hb⟩ | ⟨hret,_⟩
      · obtain ⟨b,hb⟩ := hb k (by omega)
        exact ⟨b,by rw [e3,(masked_one hq'.2 (hco4 k (by omega))).1,← vseed4_eq h (by omega)]; exact hb⟩
      · rw [hq'.2] at hret; exact absurd hret (by decide)
  · cases hqq : q
    · obtain ⟨e',he',hn⟩ := h0 hqq; exact ⟨e',by omega,hn⟩
    · rw [hqq] at hq'
      simp only [Bool.true_and,beq_eq_false_iff_ne,ne_eq] at hq'
      rcases hout with ⟨hret,_⟩ | ⟨_,k,hk,hn⟩
      · exact absurd hret hq'
      · exact ⟨4*g+k,by omega,by rw [← vseed4_eq h hk]; exact hn⟩


end VG.Proof.MlDsa.AArch64.Verify.OptimizedSamples
