import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedSamplesTwoTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedSamplesBall
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejVerified

namespace VG.Proof.MlDsa.AArch64.Verify.OptimizedSamples
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Call
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa (Params)

private theorem twoCallee {S : Nat} (hS : S<2^64) :
    CalleeOk S VG.Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.code
      (VG.Spec.MlDsa.rejNTT2Contract abi S) :=
  CalleeOk.of_verified hS VG.Proof.MlDsa.AArch64.Optimized.ResidentRej.two_verified
    (Nat.zero_le _) (by
      have hd : VG.Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.code.aarch64Depth=0 := by decide +kernel
      simp only [hd,Nat.mul_zero]; exact Nat.zero_le _)

theorem tail2_vpiece {S : Nat} (hS : S<2^64) {p : Params} (hF : VFacts p)
    (hmod : p.k*p.ℓ%4=2) :
    VPiece p S (VA p · (4*(p.k*p.ℓ/4))) (VA p · (4*(p.k*p.ℓ/4)+2))
      (VG.Impl.MlDsa.AArch64.Verify.OptimizedSamples.tail2 p) := by
  unfold VG.Impl.MlDsa.AArch64.Verify.OptimizedSamples.tail2
  refine VPiece.seq (VPiece.mono
    (VPiece.seqR (I := fun j σ s=>VS p σ (4*(p.k*p.ℓ/4)) j s) 2 0
      (fun j _ hj=>vslot2_piece hF (by omega) (by omega)))
    (fun _ _ _ h=>⟨h,fun _ h=>False.elim (Nat.not_lt_zero _ h)⟩)
    (fun _ _ _ h=>by simpa using h)) (vcall2_piece hS (twoCallee hS) hF (by omega))

theorem expAll_vpiece {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p) :
    VPiece p S (VA p · 0) (VA p · (p.k*p.ℓ))
      (VG.Impl.MlDsa.AArch64.Verify.OptimizedSamples.expAll P p) := by
  unfold VG.Impl.MlDsa.AArch64.Verify.OptimizedSamples.expAll
  have hB : VPiece p S (VA p · 0) (VA p · (4*(p.k*p.ℓ/4)))
      (seqR (VG.Impl.MlDsa.AArch64.Verify.OptimizedSamples.expA4 P p) 0 (p.k*p.ℓ/4)) := by
    simpa only [Nat.zero_add,Nat.mul_zero] using
      (VPiece.seqR (I := fun g σ s=>VA p σ (4*g) s) (p.k*p.ℓ/4) 0
        (fun g _ hg=>expA4_vpiece hP hF (by omega)))
  split
  · rename_i he
    refine VPiece.mono (VPiece.seq hB (tail2_vpiece hP.s64 hF he))
      (fun _ _ _ h=>h) (fun _ _ _ h=>?_)
    have eq : 4*(p.k*p.ℓ/4)+2=p.k*p.ℓ := by omega
    simpa only [eq] using h
  · refine VPiece.mono (VPiece.seq hB
      (VPiece.seqR (I := fun e σ s=>VA p σ e s) (p.k*p.ℓ%4) (4*(p.k*p.ℓ/4))
        (fun e _ he=>expA_vpiece hP hF (by omega)))) (fun _ _ _ h=>h) (fun _ _ _ h=>?_)
    have eq : 4*(p.k*p.ℓ/4)+p.k*p.ℓ%4=p.k*p.ℓ := by omega
    simpa only [eq] using h

theorem samples_vpiece {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p) :
    VPiece p S (fun σ s=>Z0 p p.ℓ σ s ∧ normOk p σ p.ℓ) (VB p)
      (VG.Impl.MlDsa.AArch64.Verify.OptimizedSamples.samples P p) := by
  unfold VG.Impl.MlDsa.AArch64.Verify.OptimizedSamples.samples
  exact (copyRho_vpiece hF).seq ((expAll_vpiece hP hF).seq
    ((ballCall_vpiece hP hF).seq (ballTail_vpiece hF)))

end VG.Proof.MlDsa.AArch64.Verify.OptimizedSamples
