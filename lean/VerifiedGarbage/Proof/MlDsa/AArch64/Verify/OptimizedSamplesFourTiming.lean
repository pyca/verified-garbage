import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedSamplesFour

namespace VG.Proof.MlDsa.AArch64.Verify.OptimizedSamples
open VG.Impl.MlDsa.AArch64.Call
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa (Params)
open VG.Spec.Sha3 (bytesAt)

theorem matrixMask_taint : ∀j<80,∀n∈[256,512,1024],
    (taint.check (Taint.ofRegs [.x28]) (VG.Impl.MlDsa.AArch64.Optimized.MatrixMask.code (sc (oP j)) n)
      (VG.Taint.hintOf taint (Taint.ofRegs [.x28]) (VG.Impl.MlDsa.AArch64.Optimized.MatrixMask.code (sc 0) n))).isSome=true := by
  decide +kernel

theorem vcall4_piece {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p)
    {g : Nat} (hg : 4*g+4 ≤ p.k*p.ℓ) : VPiece p S (VS p · (4*g) 4) (VA p · (4*g+4))
      (.seq (rej4At P (sc (oR4 p)) (sc oSA4) (aP (4*g))) (.seq (.block and24) (VG.Impl.MlDsa.AArch64.Optimized.MatrixMask.code (aP (4*g)) 1024))) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  refine ⟨fun _ _ hp h => vcall4_ok hP hF hp hg h,
    vrel_of (Q := fun x y => VTwo p S x y ∧ bytesAt x.mem (pa x (sc oSA4)) 136 = bytesAt y.mem (pa y (sc oSA4)) 136) ?_
      (fun _ _ _ _ hp hp' hq h h' => ⟨vc_two hF hp hp' hq h.va.vz.vc h'.va.vz.vc,by
        rw [h.seeds,h'.seeds]; simp only [seedOf,(vPub_eq hq).2.1]⟩)⟩
  have hc : rej4Chk (vR p) (vW p) (sc oSA4) (aP (4*g)) (sc (oR4 p)) = true := by unfold rej4Chk; vlay
  have ok := fun x (L : Lay S (vR p) (vW p) x) => WP.mono (rej4At_ok hP.s64 hP.rej4 L hc)
    fun _ h => (⟨_,h.1⟩ : ∃ W,PostB S x _ W)
  have tail : RelCT isa (VTwo p S) (.seq (.block and24) (VG.Impl.MlDsa.AArch64.Optimized.MatrixMask.code (aP (4*g)) 1024)) fun _ _ => True := by
    refine RelCT.seq (VTwo.step (fun _ _ h => h) (block_nomem_tr fun i hi _ => by
      simp only [and24,List.mem_singleton] at hi; subst hi; rfl) ?_)
      (taintRel [.x28] (fun _ _ h => VTwo.x28 h) (matrixMask_taint (4*g) (by omega) 1024 (by simp)))
    have f := fun z => WP.mono (and24_ok z) fun z' ⟨o,_⟩ =>
      (⟨[],postB_of_keep o.keep (by decide) (by rw [o.mem]; exact Frame.refl _ _)⟩ : ∃ W,PostB S z z' W)
    exact fun x y _ => ⟨f x,f y⟩
  exact RelCT.seq (VTwo.step (fun _ _ h => h.1)
    (rej4At_tr hP.rej4 (vOk p) hc (fun _ _ h => ⟨h.1.lx,h.1.ly,h.2,h.1.same⟩))
    (fun x y h => ⟨ok x h.1.lx,ok y h.1.ly⟩)) tail

theorem expA4_vpiece {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p)
    {g : Nat} (hg : 4*g+4 ≤ p.k*p.ℓ) : VPiece p S (VA p · (4*g)) (VA p · (4*g+4)) (VG.Impl.MlDsa.AArch64.Verify.OptimizedSamples.expA4 P p g) := by
  unfold VG.Impl.MlDsa.AArch64.Verify.OptimizedSamples.expA4
  refine VPiece.seq (VPiece.mono
    (VPiece.seqR (I := fun j σ s => VS p σ (4*g) j s) 4 0 (fun j _ hj => vslot_piece hF hg (by omega)))
      (fun _ _ _ h => ⟨h,fun _ h => False.elim (Nat.not_lt_zero _ h)⟩)
      (fun _ _ _ h => by simpa using h)) (vcall4_piece hP hF hg)

end VG.Proof.MlDsa.AArch64.Verify.OptimizedSamples
