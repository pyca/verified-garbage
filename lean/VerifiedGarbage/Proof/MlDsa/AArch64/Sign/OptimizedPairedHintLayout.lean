import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRoots
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedHintCallTiming

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Proof.MlDsa.AArch64.Optimized

theorem pairedHintReady_layout {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State}
    (L : Lay S rbs wbs s) (roots : PairedRoots S s) {c secret y high work : Ptr} {gamma : Nat}
    (hc : inB (rbs++wbs) c 1024=true) (hs : inB (rbs++wbs) secret 2048=true)
    (hh : inB (rbs++wbs) high 2048=true)
    (hy : inB (rbs++wbs) y 2048=true) (hw : inB (rbs++wbs) work 2176=true)
    (hwy : inB wbs y 2048=true) (hww : inB wbs work 2176=true)
    (hcy : sepB rbs wbs c 1024 y 2048=true) (hcw : sepB rbs wbs c 1024 work 2176=true)
    (hsy : sepB rbs wbs secret 2048 y 2048=true) (hsw : sepB rbs wbs secret 2048 work 2176=true)
    (hyw : sepB rbs wbs y 2048 work 2176=true)
    (hyh : sepB rbs wbs y 2048 high 2048=true) (hhw : sepB rbs wbs high 2048 work 2176=true)
    (hprod : pairedProductsReduced s.mem (pa s c) (pa s secret))
    (hdata : ∀j<2,ResponseDecomposed s.mem (pairPolyPtr (pa s y) j) (pairPolyPtr (pa s high) j) gamma)
    (hg : gamma∈gamma2s) :
    Paired.PairedHintReady c secret y high work gamma s := by
  refine ⟨L.nwp hc,L.nwp hs,L.nwp hy,L.nwp hh,L.nwp hw,roots.held,roots.fit,?_,L.disj hcy,L.disj hcw,
    L.disj hsy,L.disj hsw,L.disj hyw,L.disj hyh,L.disj hhw,hprod,hg,hdata,?_,?_⟩
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact roots.apart_write (L.inW hwy)
    · exact roots.apart_write (L.inW hww)
  · exact Covers.cons (L.cR hc) (Covers.cons (L.cR hs)
      (Covers.cons (L.cR hh) (Covers.cons roots.readable (Covers.cons (L.cR hy) (L.cR hw)))))
  · exact Covers.cons (L.cW hwy) (L.cW hww)

end VG.Proof.MlDsa.AArch64.Sign
