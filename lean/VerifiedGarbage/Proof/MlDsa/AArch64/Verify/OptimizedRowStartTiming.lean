import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedRowState

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen VG.Proof.MlDsa.AArch64.Optimized

theorem unpack_tr {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p)
    {r : Nat} (hr : r<p.k) :
    RelCT isa (RootPair p S (RowI p S r 0)) (unpackT1At P (.x25,32+320*r) (tmP p))
      (RootPair p S (RowI p S r 1)) := by
  refine rootPair_progress (fun σ s hp ⟨h,A,c,q,hs,hw⟩=>
    WP.mono (unpack_ok hP hF hp hr hs hw) fun _ ht=>⟨h,A,c,q,ht⟩) ?_
  have hk:=hF.k;have hl:=hF.l;have hkl:=hF.kl;have hsc:=hF.scr;have hpk:=hF.pk
  have hc : rwChk (vR p) (vW p) (.x25,32+320*r) 320 (tmP p) 1024=true := by unfold rwChk;vlay
  apply t1At_tr hP.unpackT1 (vOk p) hc
  intro x y hh
  obtain ⟨⟨σ,τ,hσ,hτ,pub,⟨h,A,c,q,hx,_⟩,⟨h',A',c',q',hy,_⟩⟩,_⟩:=hh
  have H:=vc_two hF hσ hτ pub hx.vc hy.vc
  exact ⟨H.lx,H.ly,H.same⟩

theorem nttT_tr {p : Params} (hF : VFacts p) {S r : Nat} (hr : r<p.k) :
    RelCT isa (RootPair p S (RowI p S r 1)) (Impl.MlDsa.AArch64.Verify.Optimized.forward (tmP p))
      (RootPair p S (RowI p S r 2)) := by
  refine rootPair_progress (fun σ s hp ⟨h,A,c,q,hs,hw,ht⟩=>
    WP.mono (nttT_ok hF hp hr hs hw ht) fun _ hv=>⟨h,A,c,q,hv⟩) ?_
  unfold Impl.MlDsa.AArch64.Verify.Optimized.forward
  apply positiveNttAt_tr (S:=S) (ptr_ok (show Reg.x28∈keptRegs from by decide))
  intro x y hh
  obtain ⟨⟨σ,τ,hσ,hτ,pub,⟨h,A,c,q,hx,_,tx⟩,⟨h',A',c',q',hy,_,ty⟩⟩,et⟩:=hh
  have H:=vc_two hF hσ hτ pub hx.vc hy.vc
  have hk:=hF.k;have hl:=hF.l;have hkl:=hF.kl;have hsc:=hF.scr
  have rd : inB (vR p++vW p) (tmP p) 1024=true := by vlay
  have wr : inB (vW p) (tmP p) 1024=true := by vlay
  exact ⟨forward_ready hF hσ hx.vc hx.roots rd wr tx.1,
    forward_ready hF hτ hy.vc hy.roots rd wr ty.1,
    H.same.pa (show Reg.x28∈bases from by decide),H.same.2,et.1⟩
end VG.Proof.MlDsa.AArch64.Verify.Optimized
