import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedSamplesFourTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedSamplesTwo

namespace VG.Proof.MlDsa.AArch64.Verify.OptimizedSamples
open VG.Impl.MlDsa.AArch64.Call
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG.Spec.MlDsa (Params)
open VG.Spec.Sha3 (bytesAt)

theorem vseeds2 {p : Params} {σ : State} {e : Nat} {s : State} (h : VS p σ e 2 s) :
    bytesAt s.mem (pa s (sc oSA4)) 68=seedOf p σ e++seedOf p σ (e+1) := by
  rw [show 68=34+34 from rfl,Proof.MlKem.bytesAt_add]
  have h0 := vseed2_eq h (k := 0) (by decide)
  have h1 := vseed2_eq h (k := 1) (by decide)
  simp only [Spec.MlDsa.seed4,Nat.mul_zero,Nat.add_zero,Nat.mul_one,
    VG.Proof.MlKem.AArch64.ptr_zero] at h0 h1
  rw [h0,h1]

theorem vcall2_piece {S : Nat} (hS : S<2^64) {cd : Prog isa} {nm : String}
    (C : CalleeOk S cd (VG.Spec.MlDsa.rejNTT2Contract AArch64.abi S)) {p : Params} (hF : VFacts p)
    {e : Nat} (he : e+2 ≤ p.k*p.ℓ) : VPiece p S (VS p · (e) 2) (VA p · (e+2))
      (.seq (callAt nm cd (rej2Args (sc oSA4) (aP e) (sc (oR4 p)))) (.seq (.block and24) (VG.Impl.MlDsa.AArch64.Optimized.MatrixMask.code (aP (e)) 512))) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  refine ⟨fun _ _ hp h => vcall2_ok hS C hF hp he h,
    vrel_of (Q := fun x y => VTwo p S x y ∧ bytesAt x.mem (pa x (sc oSA4)) 68 = bytesAt y.mem (pa y (sc oSA4)) 68) ?_
      (fun _ _ _ _ hp hp' hq h h' => ⟨vc_two hF hp hp' hq h.va.vz.vc h'.va.vz.vc,by
        rw [vseeds2 h,vseeds2 h']; simp only [seedOf,(vPub_eq hq).2.1]⟩)⟩
  have hc : rej2Chk (vR p) (vW p) (sc oSA4) (aP (e)) (sc (oR4 p)) = true := by unfold rej2Chk; vlayd
  have ok := fun x (L : Lay S (vR p) (vW p) x) => WP.mono (rej2At_ok hS C L (nm := nm) hc)
    fun _ h => (⟨_,h.1⟩ : ∃ W,PostB S x _ W)
  have tail : RelCT isa (VTwo p S) (.seq (.block and24) (VG.Impl.MlDsa.AArch64.Optimized.MatrixMask.code (aP (e)) 512)) fun _ _ => True := by
    refine RelCT.seq (VTwo.step (fun _ _ h => h) (block_nomem_tr fun i hi _ => by
      simp only [and24,List.mem_singleton] at hi; subst hi; rfl) ?_)
      (taintRel [.x28] (fun _ _ h => VTwo.x28 h) (matrixMask_taint (e) (by omega) 512 (by simp)))
    have f := fun z => WP.mono (and24_ok z) fun z' ⟨o,_⟩ =>
      (⟨[],postB_of_keep o.keep (by decide) (by rw [o.mem]; exact Frame.refl _ _)⟩ : ∃ W,PostB S z z' W)
    exact fun x y _ => ⟨f x,f y⟩
  exact RelCT.seq (VTwo.step (fun _ _ h => h.1)
    (rej2At_tr (nm := nm) C (vOk p) hc (fun _ _ h => ⟨h.1.lx,h.1.ly,h.2,h.1.same⟩))
    (fun x y h => ⟨ok x h.1.lx,ok y h.1.ly⟩)) tail


end VG.Proof.MlDsa.AArch64.Verify.OptimizedSamples
