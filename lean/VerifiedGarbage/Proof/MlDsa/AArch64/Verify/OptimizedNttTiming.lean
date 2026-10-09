import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedNtt
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedTimingBase

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Impl.MlDsa.AArch64.Verify.Optimized
open VG.Proof.MlDsa.AArch64.KeyGen VG.Proof.MlDsa.AArch64.Optimized
open VG.Impl.MlDsa.AArch64.Call (Ptr)

theorem forward_ready {p : Params} (hF : VFacts p) {S : Nat} {σ s : State}
    (hp : vPre p S σ) {a : Ptr} (hc : VC p σ s) (roots : Sign.StaticRoots S s)
    (hr : inB (vR p++vW p) a 1024=true) (hw : inB (vW p) a 1024=true)
    (red : Reduced s.mem (pa s a)) : NttCallReady a s := by
  have L := hc.lay hF hp
  exact ⟨L.nwp hr,roots.nttTableAt (L.inW hw),red,
    Covers.cons roots.forward.readable (L.cR hr),L.cW hw⟩

theorem nttZ_tr {p : Params} (hF : VFacts p) {S i : Nat} (hi : i<p.ℓ) :
    RelCT isa (RootPair p S (SCx p S i false 0)) (forward (zP p i))
      (RootPair p S (SCx p S (i+1) false 0)) := by
  refine rootPair_progress (fun σ s hp ⟨h,A,c,q,hs⟩=>
    WP.mono (nttZ_ok hF hp hi hs) fun _ ht=>⟨h,A,c,q,ht⟩) ?_
  unfold forward
  apply positiveNttAt_tr (S := S) (ptr_ok (show Reg.x28∈keptRegs from by decide))
  intro x y hh
  obtain ⟨⟨σ,τ,hσ,hτ,pub,⟨h,A,c,q,hx⟩,⟨h',A',c',q',hy⟩⟩,et⟩ := hh
  have H := vc_two hF hσ hτ pub hx.vc hy.vc
  have hk:=hF.k;have hl:=hF.l;have hkl:=hF.kl;have hsc:=hF.scr
  have hr : inB (vR p++vW p) (zP p i) 1024=true := by vlayd
  have hw : inB (vW p) (zP p i) 1024=true := by vlayd
  have red {σ s : State} {h A c q} (hs : SC p S σ h A c q i false 0 s) :
      Reduced s.mem (pa s (zP p i)) := by
    have hz:=hs.z i hi
    simp only [Stored,decide_eq_false_iff_not.mpr (Nat.lt_irrefl i),Bool.false_eq_true,↓reduceIte] at hz
    exact hz.1
  exact ⟨forward_ready hF hσ hx.vc hx.roots hr hw (red hx),
    forward_ready hF hτ hy.vc hy.roots hr hw (red hy),
    H.same.pa (show Reg.x28∈bases from by decide),H.same.2,et.1⟩

theorem nttC_tr {p : Params} (hF : VFacts p) {S : Nat} :
    RelCT isa (RootPair p S (SCx p S p.ℓ false 0)) (forward (cP p))
      (RootPair p S (SCx p S p.ℓ true 0)) := by
  refine rootPair_progress (fun σ s hp ⟨h,A,c,q,hs⟩=>
    WP.mono (nttC_ok hF hp hs) fun _ ht=>⟨h,A,c,q,ht⟩) ?_
  unfold forward
  apply positiveNttAt_tr (S := S) (ptr_ok (show Reg.x28∈keptRegs from by decide))
  intro x y hh
  obtain ⟨⟨σ,τ,hσ,hτ,pub,⟨h,A,c,q,hx⟩,⟨h',A',c',q',hy⟩⟩,et⟩ := hh
  have H := vc_two hF hσ hτ pub hx.vc hy.vc
  have hk:=hF.k;have hl:=hF.l;have hkl:=hF.kl;have hsc:=hF.scr
  have hr : inB (vR p++vW p) (cP p) 1024=true := by vlayd
  have hw : inB (vW p) (cP p) 1024=true := by vlayd
  exact ⟨forward_ready hF hσ hx.vc hx.roots hr hw hx.c.1,
    forward_ready hF hτ hy.vc hy.roots hr hw hy.c.1,
    H.same.pa (show Reg.x28∈bases from by decide),H.same.2,et.1⟩
end VG.Proof.MlDsa.AArch64.Verify.Optimized
