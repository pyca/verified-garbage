import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedNtt
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedFinish
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedTimingBase
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttCallTiming

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Spec.MlDsa VG.Impl.MlDsa.AArch64.KeyGen
open VG.Proof.MlDsa.AArch64.Optimized
open VG.Impl.MlDsa.AArch64.Call (Arg)

theorem nttSecret_ready {p : Params} (hF : PFacts p) {S' : Nat} {σ s : State}
    (hp : kgPre p S' σ) {j : Nat} (hj : j<p.ℓ)
    (h : KRx p (p.ℓ+p.k) j 0 σ s) (roots : Sign.StaticRoots S' s) :
    NttCallReady (sP p j) s := by
  obtain ⟨A,T,R,h⟩ := h
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  have L := h.kc.lay hF hp
  have hr : inB (kgR++kgW p) (sP p j) 1024=true := by layd
  have hw : inB (kgW p) (sP p j) 1024=true := by layd
  have hv := h.s1 j hj
  simp only [ite_eq_right (Nat.lt_irrefl j)] at hv
  exact ⟨L.nwp hr,roots.nttTableAt (L.inW hw),hv.1,
    Covers.cons roots.forward.readable (L.cR hr),L.cW hw⟩

theorem nttSecret_tr {p : Params} (hF : PFacts p) {S' : Nat} {j : Nat} (hj : j<p.ℓ) :
    RelCT isa (RootPair p S' (KRx p (p.ℓ+p.k) j 0))
      (Impl.MlDsa.AArch64.KeyGen.Optimized.nttSecret p j) fun _ _ => True := by
  apply positiveNttAt_tr (S := S') (show (Arg.ptr (sP p j)).Ok from ptr_ok (show Reg.x28∈keptRegs from by decide))
  rintro x y ⟨⟨σ,τ,hσ,hτ,pub,⟨hx,rx⟩,⟨hy,ry⟩⟩,et⟩
  obtain ⟨A,T,R,hx'⟩ := hx
  obtain ⟨B,U,V,hy'⟩ := hy
  have ht := kc_two hF hσ hτ pub hx'.kc hy'.kc
  exact ⟨nttSecret_ready hF hσ hj ⟨A,T,R,hx'⟩ rx,
    nttSecret_ready hF hτ hj ⟨B,U,V,hy'⟩ ry,
    ht.same.pa (show Reg.x28∈bases from by decide),ht.same.2,et.1⟩

theorem nttSecret_relCT {p : Params} (hF : PFacts p) {S' : Nat} {j : Nat} (hj : j<p.ℓ) :
    RelCT isa (RootPair p S' (KRx p (p.ℓ+p.k) j 0))
      (Impl.MlDsa.AArch64.KeyGen.Optimized.nttSecret p j)
      (RootPair p S' (KRx p (p.ℓ+p.k) (j+1) 0)) := by
  apply rootPair_progress (ht := nttSecret_tr hF hj)
  rintro σ s hp ⟨A,T,R,h⟩ roots
  exact WP.mono (nttSecret_ok hF hp hj h roots) fun t ht => ⟨⟨A,T,R,ht.1⟩,ht.2⟩

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized
