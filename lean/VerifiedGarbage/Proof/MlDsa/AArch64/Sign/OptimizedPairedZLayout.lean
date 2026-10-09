import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRoots
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedZCheck

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Proof.MlDsa.AArch64.Optimized

theorem pairedZReady_layout {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State}
    (L : Lay S rbs wbs s) (roots : PairedRoots S s) {c secret y work : Ptr} {B : Nat}
    (hc : inB (rbs++wbs) c 1024=true) (hs : inB (rbs++wbs) secret 2048=true)
    (hy : inB (rbs++wbs) y 2048=true) (hw : inB (rbs++wbs) work 2176=true)
    (hwy : inB wbs y 2048=true) (hww : inB wbs work 2176=true)
    (hcy : sepB rbs wbs c 1024 y 2048=true) (hcw : sepB rbs wbs c 1024 work 2176=true)
    (hsy : sepB rbs wbs secret 2048 y 2048=true) (hsw : sepB rbs wbs secret 2048 work 2176=true)
    (hyw : sepB rbs wbs y 2048 work 2176=true)
    (hprod : pairedProductsReduced s.mem (pa s c) (pa s secret))
    (hdata : ∀j<2,Reduced s.mem (pairPolyPtr (pa s y) j)) (hB : 1≤B) (hB' : B≤524288) :
    Paired.PairedZReady c secret y work B s := by
  refine ⟨L.nwp hc,L.nwp hs,L.nwp hy,L.nwp hw,roots.held,roots.fit,?_,L.disj hcy,L.disj hcw,
    L.disj hsy,L.disj hsw,L.disj hyw,hprod,hdata,hB,hB',?_,?_⟩
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact roots.apart_write (L.inW hwy)
    · exact roots.apart_write (L.inW hww)
  · exact Covers.cons (L.cR hc) (Covers.cons (L.cR hs)
      (Covers.cons roots.readable (Covers.cons (L.cR hy) (L.cR hw))))
  · exact Covers.cons (L.cW hwy) (L.cW hww)

theorem pairedZAt_layout {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State}
    (L : Lay S rbs wbs s) {c secret y work : Ptr} {gamma B : Nat}
    (hc : inB (rbs++wbs) c 1024=true) (hs : inB (rbs++wbs) secret 2048=true)
    (hy : inB (rbs++wbs) y 2048=true) (hw : inB (rbs++wbs) work 2176=true)
    (h : Paired.PairedZReady c secret y work B s) :
    WP isa (callAt "vg_mldsa_fused_pair_z" (VG.Impl.MlDsa.AArch64.Optimized.Paired.selected .z)
      (Paired.pairedZArgs c secret y work work gamma B)) s fun t =>
      PPostB S s t [(y,2048),(work,2176)] ∧ t.gpr .x24=s.gpr .x24 ∧
      (∀j<2,SignedPolyIs t.mem (pairPolyPtr (pa s y) j)
        (add (polyAt s.mem (pairPolyPtr (pa s y) j)) (pairedProduct s.mem (pa s c) (pa s secret) j))
          (-(q:Int)+1) ((q:Int)-1)) ∧
      (t.gpr .x0).setWidth 32=if normRq ((List.range 2).map fun j =>
        add (polyAt s.mem (pairPolyPtr (pa s y) j)) (pairedProduct s.mem (pa s c) (pa s secret) j))<B then 1 else 0 := by
  refine WP.mono (Paired.pairedZAt_ok L.s64 (ptr_ok (L.ptrBs hc)) (ptr_ok (L.ptrBs hs))
    (ptr_ok (L.ptrBs hy)) (ptr_ok (L.ptrBs hw)) (ptr_ok (L.ptrBs hw)) h) fun t ⟨hp,hfields,hret⟩ => ?_
  exact ⟨hp.b,hp.cs .x24 (by decide) (by decide),fun j hj => centered_signed (hfields j hj).1 (hfields j hj).2,hret⟩

end VG.Proof.MlDsa.AArch64.Sign
