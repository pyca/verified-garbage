import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.MaskPairStep

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (seqR)
open VG.Proof.MlDsa.Sign VG.Spec.MlDsa

def masksPairChk (p : Params) : Bool :=
  (List.range (p.ℓ/2)).all (fun j => maskPairStepChk p (2*j)) &&
  (List.range p.ℓ).all (mChk p)

theorem masksPairChk_ok {p : Params} (h : Ok3 p) : masksPairChk p=true := by
  rcases h with rfl | rfl | rfl <;> decide +kernel

theorem masksPaired_ok {P : Prims} {D : Nat} (hP : PrimsOk P D)
    {nm : String} {cd : Prog isa} (C : CalleeOk D cd (expandMaskPairContract AArch64.abi D))
    {p : Params} {σ s : State} {t : Nat} (hc : masksPairChk p=true)
    (h : IL p D σ t s) :
    WP isa (masksPaired P p nm cd) s (ICm p D σ t p.ℓ) := by
  simp only [masksPairChk,Bool.and_eq_true,List.all_eq_true,List.mem_range] at hc
  unfold masksPaired
  refine WP.seq (WP.mono (seqR_ok (I := fun j => ICm p D σ t (2*j)) (p.ℓ/2) 0
    (fun j _ hj u hu => ?_) s ⟨h,fun _ h => by omega,fun _ h => by omega⟩) fun a ha => ?_)
  · simpa only [Nat.mul_add,Nat.mul_one] using maskPairR_ok hP C (hc.1 j (by omega)) hu
  · have he : 2*(p.ℓ/2)+p.ℓ%2=p.ℓ := by omega
    rw [Nat.zero_add] at ha
    have hw := seqR_ok (I := fun r => ICm p D σ t r) (p.ℓ%2) (2*(p.ℓ/2))
      (fun r _ hr u hu => maskR_ok hP (hc.2 r (by omega)) hu) a ha
    simpa only [he] using hw

theorem masks_ok {P : Prims} {D : Nat} (hP : PrimsOk P D)
    {p : Params} {σ s : State} {t : Nat} (hc : masksPairChk p=true) (h : IL p D σ t s) :
    WP isa (masks P p) s (ICm p D σ t p.ℓ) := by
  unfold masks
  split
  · exact masksPaired_ok hP hP.expandMaskPair hc h
  · simp only [masksPairChk,Bool.and_eq_true,List.all_eq_true,List.mem_range] at hc
    simpa only [Nat.zero_add] using seqR_ok (I := fun r => ICm p D σ t r) p.ℓ 0
      (fun r _ hr _ hh => maskR_ok hP (hc.2 r (by omega)) hh) s
      ⟨h,fun _ h => by omega,fun _ h => by omega⟩

end VG.Proof.MlDsa.AArch64.Sign
