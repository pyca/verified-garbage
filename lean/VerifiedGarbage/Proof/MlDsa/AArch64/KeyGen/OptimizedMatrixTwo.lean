import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Samp4
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedCallTwo
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedMatrixSeeds
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MatrixMask

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG.Impl.MlDsa.AArch64.Call
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa (Params Poly rejNTTPoly coeffAt polyAt Reduced PolyIs poly4 seed4 minBounds)
open VG.Proof.MlDsa.KeyGen (seedA ifp ifn masked_one masked_zero)
open VG.Spec.Sha3 (bytesAt)

theorem seed2_eq {p : Params} {σ : State} {e : Nat} {s : State} (h : GS p σ e 2 s) {k : Nat} (hk : k<2) :
    seed4 s.mem (pa s (sc oSA4)) k=seedA (rhoOf p σ) ((e+k)/p.ℓ) ((e+k)%p.ℓ) := by
  unfold seed4
  rw [show pa s (sc oSA4)+BitVec.ofNat 64 (34*k)=pa s (sc (oSA4+34*k)) from sc_add _ _ _]
  exact h.done k hk

theorem bound2 {ρ : Nat→List Byte} {x : Nat→Poly}
    (h : ∀k<2,∃b : Spec.MlDsa.Bounds,rejNTTPoly b.rejNTT (ρ k)=some (x k)) :
    ∃n,∀k<2,rejNTTPoly n (ρ k)=some (x k) := by
  obtain ⟨b0,h0⟩ := h 0 (by decide)
  obtain ⟨b1,h1⟩ := h 1 (by decide)
  refine ⟨max b0.rejNTT b1.rejNTT,fun k hk => ?_⟩
  rcases (by omega : k=0 ∨ k=1) with rfl | rfl
  · exact Proof.MlDsa.KeyGen.rejNTTPoly_mono (by omega) h0
  · exact Proof.MlDsa.KeyGen.rejNTTPoly_mono (by omega) h1

theorem matrixTwo_ok {S : Nat} (hS : S<2^64) {cd : Prog isa} {nm : String}
    (C : CalleeOk S cd (VG.Spec.MlDsa.rejNTT2Contract AArch64.abi S)) {p : Params} (hF : PFacts p)
    {σ : State} (hp : kgPre p S σ) {e : Nat} (he : e+2 ≤ p.k*p.ℓ) {s : State}
    (h : GS p σ e 2 s) (hr : MatrixPrefixes p σ 4 s) :
    WP isa (.seq (callAt nm cd (rej2Args (sc oSA4) (aP e) (sc (oR4 p))))
      (.seq (.block and24) (VG.Impl.MlDsa.AArch64.Optimized.MatrixMask.code (aP (e)) 512))) s (fun t => KSamp p σ (e+2) 0 t ∧ MatrixPrefixes p σ 4 t) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  have L := h.ks.k1.kc.lay hF hp
  refine WP.seq (WP.mono (rej2At_ok hS C L
    (seed := sc oSA4) (a := aP (e)) (ss := sc (oR4 p)) (by unfold rej2Chk; lay))
    fun s2 ⟨hP2,h24,hred,hout⟩ => ?_)
  have L2 := L.post hP2
  have hr01 : (s2.gpr .x0).setWidth 32 = 0 ∨ (s2.gpr .x0).setWidth 32 = 1 := by
    rcases hout with ⟨h1,_⟩ | ⟨h0,_⟩
    exacts [.inr h1,.inl h0]
  refine WP.seq (WP.mono (and24_ok s2) fun s20 ⟨h20,e24⟩ => ?_)
  have hP20 : PPostB S s2 s20 [] := postB_of_keep h20.keep (by decide)
    (by rw [h20.mem]; exact Frame.refl _ _)
  have L20 := L2.post hP20
  have hr20 : (s20.gpr .x0).setWidth 32 = 0 ∨ (s20.gpr .x0).setWidth 32 = 1 := by
    rw [h20.get .x0]; exact hr01
  refine WP.mono (VG.Proof.MlDsa.AArch64.Optimized.MatrixMask.mask_ok L20 (a := aP (e)) (N := 32) (by decide) (by decide) (by lay) (by lay) hr20)
    fun s3 ⟨hP3,k3,hco⟩ => ?_
  have hP23 := PPostB.app hP20 hP3 (sc_bases _ (by simp))
  have hP13 := PPostB.app hP2 hP23 (sc_bases _ (by simp))
  refine ⟨?_,hr.keep L hP13 (fun k hk => by lay)⟩
  have e2 : pa s2 (aP (e)) = pa s (aP (e)) := sc_pa hP2 _
  have e20 : pa s20 (aP (e)) = pa s2 (aP (e)) := sc_pa hP20 _
  rw [h20.get .x0,e20,e2,h20.mem] at hco
  have hco4 : ∀ k < 2, ∀ i < 256,coeffAt s3.mem (poly4 (pa s (aP (e))) k) i =
      if (s2.gpr .x0).setWidth 32 = 1 then coeffAt s2.mem (poly4 (pa s (aP (e))) k) i else 0 :=
    fun k hk i hi => by rw [coeffAt_poly4,coeffAt_poly4]; exact hco _ (by omega)
  have e3 : ∀ k,pa s3 (aP (e+k)) = poly4 (pa s (aP (e))) k := fun k => by
    rw [pa_poly4,sc_pa hP13]
  obtain ⟨A,S',hA,_,hG⟩ := h.ks.ex
  have h24' : s3.gpr .x24 = if s.gpr .x24 = 1 ∧ (s2.gpr .x0).setWidth 32 = 1 then 1 else 0 := by
    rw [k3.get .x24,e24,h24,Proof.MlDsa.KeyGen.and01 (good_01 hG) hr01]
  refine ⟨h.ks.k1.step hF hp hP13 (by unfold k1Chk kcChk; lay),
    fun e' => if e' < e then A e' else polyAt s3.mem (pa s3 (aP e')),S',
    fun e' he' => ?_,fun _ h => False.elim (Nat.not_lt_zero _ h),?_⟩
  · dsimp only
    by_cases hlt : e' < e
    · rw [ifp hlt]
      exact L.keepPoly hP13 (by lay) (hA e' hlt)
    · rw [ifn hlt]
      refine ⟨?_,rfl⟩
      obtain ⟨k,rfl⟩ : ∃ k,e' = e+k := ⟨e'-e,by omega⟩
      rw [e3]
      by_cases h1 : (s2.gpr .x0).setWidth 32 = 1
      · exact (masked_one h1 (hco4 k (by omega))).2 (hred h1 k (by omega))
      · exact (masked_zero h1 (hco4 k (by omega))).1
  · rw [h24']
    rcases hG with ⟨h1,b,hb,_⟩ | ⟨h0,hn⟩
    · rcases hout with ⟨ho,hb4⟩ | ⟨ho,k,hk,hn⟩
      · obtain ⟨n,hn⟩ := bound2 hb4
        refine .inl ⟨by rw [ifp ⟨h1,ho⟩],{ b with rejNTT := max b.rejNTT n },fun e' he' => ?_,
          fun _ h => False.elim (Nat.not_lt_zero _ h)⟩
        dsimp only
        by_cases hlt : e' < e
        · rw [ifp hlt]
          exact Proof.MlDsa.KeyGen.rejNTTPoly_mono (Nat.le_max_left _ _) (hb e' hlt)
        · rw [ifn hlt]
          obtain ⟨k,rfl⟩ : ∃ k,e' = e+k := ⟨e'-e,by omega⟩
          have hk : k < 2 := by omega
          rw [e3,(masked_one ho (hco4 k hk)).1,← seed2_eq h hk]
          exact Proof.MlDsa.KeyGen.rejNTTPoly_mono (Nat.le_max_right _ _) (hn k hk)
      · rw [ifn (fun h => by rw [h.2] at ho; exact absurd ho (by decide))]
        rw [seed2_eq h hk] at hn
        have hq : (e+k)/p.ℓ < p.k := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm p.ℓ p.k]; omega)
        exact .inr ⟨rfl,Proof.MlDsa.KeyGen.keyGenInternal_none_A hq (Nat.mod_lt _ (by omega)) hn⟩
    · rw [ifn (fun h => by rw [h.1] at h0; exact absurd h0 (by decide))]
      exact .inr ⟨rfl,hn⟩

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized
