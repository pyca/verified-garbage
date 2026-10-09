import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedRowStartTiming

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen VG.Proof.MlDsa.AArch64.Optimized

theorem product_tr {p : Params} (hF : VFacts p) {S r : Nat} (hr : r<p.k) :
    RelCT isa (RootPair p S (RowI p S r 2)) (Impl.MlDsa.AArch64.Verify.Optimized.product p)
      (RootPair p S (RowI p S r 3)) := by
  refine rootPair_progress (fun σ s hp ⟨h,A,c,q,hs,hw,ht⟩=>
    WP.mono (product_ok hF hp hr hs hw ht) fun _ hv=>⟨h,A,c,q,hv⟩) ?_
  unfold Impl.MlDsa.AArch64.Verify.Optimized.product
  apply MontProduct.at_tr (S:=S) (ptr_ok (show Reg.x28∈keptRegs from by decide))
    (ptr_ok (show Reg.x28∈keptRegs from by decide)) (ptr_ok (show Reg.x28∈keptRegs from by decide))
  intro x y hh
  obtain ⟨⟨σ,τ,hσ,hτ,pub,⟨h,A,c,q,hx,wx,tx⟩,⟨h',A',c',q',hy,wy,ty⟩⟩,_⟩:=hh
  have H:=vc_two hF hσ hτ pub hx.vc hy.vc
  exact ⟨product_ready hF hσ hr hx wx tx,product_ready hF hτ hr hy wy ty,
    H.same.pa (show Reg.x28∈bases from by decide),H.same.pa (show Reg.x28∈bases from by decide),
    H.same.pa (show Reg.x28∈bases from by decide),H.same.2⟩

theorem subtract_tr {p : Params} (hF : VFacts p) {S r : Nat} (hS : S<2^64) (hr : r<p.k) :
    RelCT isa (RootPair p S (RowI p S r 3)) (Impl.MlDsa.AArch64.Verify.Optimized.subtract p)
      (RootPair p S (RowI p S r 4)) := by
  refine rootPair_progress (fun σ s hp ⟨h,A,c,q,hs,hw,ht⟩=>
    WP.mono (subtract_ok hF hp hr hs hw ht) fun _ hv=>⟨h,A,c,q,hv⟩) ?_
  have hk:=hF.k;have hl:=hF.l;have hkl:=hF.kl;have hsc:=hF.scr
  have hc : accChk (vR p) (vW p) (wP p) (tm2P p)=true := by unfold accChk;vlay
  have C : CalleeOk S (Impl.MlDsa.AArch64.Optimized.AddSub.code true) (subContract abi S) :=
    CalleeOk.of_verified hS AddSub.sub_verified (Nat.zero_le _) (by change 0≤S;omega)
  apply accAt_tr (op:=sub) C (vOk p) hc
  intro x y hh
  obtain ⟨⟨σ,τ,hσ,hτ,pub,⟨h,A,c,q,hx,wx,tx⟩,⟨h',A',c',q',hy,wy,ty⟩⟩,_⟩:=hh
  have H:=vc_two hF hσ hτ pub hx.vc hy.vc
  exact ⟨H.lx,H.ly,⟨wx.1,tx.1⟩,⟨wy.1,ty.1⟩,H.same⟩

theorem inverse_tr {p : Params} (hF : VFacts p) {S r : Nat} (hr : r<p.k) :
    RelCT isa (RootPair p S (RowI p S r 4)) (Impl.MlDsa.AArch64.Verify.Optimized.inverse (wP p))
      (RootPair p S (RowI p S r 5)) := by
  refine rootPair_progress (fun σ s hp ⟨h,A,c,q,hs,hw⟩=>
    WP.mono (inverse_ok hF hp hr hs hw) fun _ hv=>⟨h,A,c,q,hv⟩) ?_
  unfold Impl.MlDsa.AArch64.Verify.Optimized.inverse
  apply Inverse.inverseSingleAt_tr (S:=S) (ptr_ok (show Reg.x28∈keptRegs from by decide))
  intro x y hh
  obtain ⟨⟨σ,τ,hσ,hτ,pub,⟨h,A,c,q,hx,wx⟩,⟨h',A',c',q',hy,wy⟩⟩,et⟩:=hh
  have H:=vc_two hF hσ hτ pub hx.vc hy.vc
  exact ⟨inverse_ready hF hσ hr hx wx,inverse_ready hF hτ hr hy wy,
    H.same.pa (show Reg.x28∈bases from by decide),H.same.2,et.2⟩
end VG.Proof.MlDsa.AArch64.Verify.Optimized
