import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedRowStart
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MontProductCallTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.AddSubVerified

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Proof.MlDsa.AArch64.Optimized
open VG.Proof.MlDsa.Arith.Montgomery

theorem product_ok {p : Params} (hF : VFacts p) {S : Nat} {σ s : State} (hp : vPre p S σ)
    {h : List (Vector Bool n)} {A' : Nat→Nat→Poly} {c0 : Poly} {q : Bool} {r : Nat} (hr : r<p.k)
    (hs : SC p S σ h A' c0 q p.ℓ true r s) (hw : W p σ A' r s)
    (ht : PosPolyIs s.mem (pa s (tmP p)) (Proof.MlDsa.Verify.t1Hat (vPk p σ) r)) :
    WP isa (Impl.MlDsa.AArch64.Verify.Optimized.product p) s fun t=>
      SC p S σ h A' c0 q p.ℓ true r t ∧ W p σ A' r t ∧
      PolyIs t.mem (pa t (tm2P p))
        (montgomeryMultiplyNTT (ntt c0) (Proof.MlDsa.Verify.t1Hat (vPk p σ) r)) := by
  have L:=hs.vc.lay hF hp
  have hk:=hF.k;have hl:=hF.l;have hkl:=hF.kl;have hsc:=hF.scr
  have hc : PosPolyIs s.mem (pa s (cP p)) (ntt c0) := hs.c
  have ro : inB (vR p++vW p) (tm2P p) 1024=true := by vlayd
  have ra : inB (vR p++vW p) (cP p) 1024=true := by vlayd
  have rb : inB (vR p++vW p) (tmP p) 1024=true := by vlayd
  have wo : inB (vW p) (tm2P p) 1024=true := by vlayd
  have ready : MontProduct.Ready (tm2P p) (cP p) (tmP p) s :=
    ⟨L.nwp ro,L.nwp ra,L.nwp rb,L.disj (by vlayd),L.disj (by vlayd),hc.bound,ht.bound,
      Covers.cons (L.cR ra) (Covers.cons (L.cR rb) (L.cR ro)),L.cW wo⟩
  refine WP.mono_syms (MontProduct.at_ok L.s64 (ptr_ok (L.ptrBs ro)) (ptr_ok (L.ptrBs ra))
    (ptr_ok (L.ptrBs rb)) ready) fun t ⟨hp',hv⟩ hy=>?_
  have hb : PPostB S s t [(tm2P p,1024)] := hp'.b
  refine ⟨hs.keep hF hp hb (by scchks hF (Nat.le_of_lt hr)) hy
    (fun w hm=>by obtain rfl:=List.mem_singleton.mp hm;exact wo)
    (hp'.cs .x24 (by decide) (by decide)),L.keepPoly hb (by vlayd) hw,?_⟩
  rw [hb.pa (L.ptrBs ro)]
  rwa [hc.value,ht.value] at hv

end VG.Proof.MlDsa.AArch64.Verify.Optimized
