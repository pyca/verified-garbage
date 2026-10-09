import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedCalls
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowCallTiming

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Proof.MlDsa.AArch64.Optimized

theorem pairedLowReady_layout {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State}
    (L : Lay S rbs wbs s) {c secret out low work : Ptr} {g B : Nat}
    (hc : inB (rbs++wbs) c 1024=true)
    (hsecret : inB (rbs++wbs) secret 2048=true)
    (hout : inB (rbs++wbs) out 2048=true)
    (hlow : inB (rbs++wbs) low 2048=true)
    (hwork : inB (rbs++wbs) work 2176=true)
    (hwout : inB wbs out 2048=true)
    (hwlow : inB wbs low 2048=true)
    (hwwork : inB wbs work 2176=true)
    (hc_out : sepB rbs wbs c 1024 out 2048=true)
    (hc_low : sepB rbs wbs c 1024 low 2048=true)
    (hc_work : sepB rbs wbs c 1024 work 2176=true)
    (hsecret_out : sepB rbs wbs secret 2048 out 2048=true)
    (hsecret_low : sepB rbs wbs secret 2048 low 2048=true)
    (hsecret_work : sepB rbs wbs secret 2048 work 2176=true)
    (hout_low : sepB rbs wbs out 2048 low 2048=true)
    (hout_work : sepB rbs wbs out 2048 work 2176=true)
    (hlow_work : sepB rbs wbs low 2048 work 2176=true)
    (held : ∀i<512,s.mem.readW (s.syms "VG_MLDSA_INV_PAIR"+BitVec.ofNat 64 (8*i)) 64=
      VG.Impl.MlDsa.AArch64.Optimized.Paired.expandedWords.getD i 0)
    (hfit : (s.syms "VG_MLDSA_INV_PAIR").toNat+4096≤2^64)
    (hsep : ∀r∈[⟨pa s out,2048⟩,⟨pa s low,2048⟩,⟨pa s work,2176⟩],
      (⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩:Region).Disjoint r)
    (ht : Covers [⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩] (s.rd++s.wr))
    (hprod : pairedProductsReduced s.mem (pa s c) (pa s secret))
    (hdata : ∀j<2,Reduced s.mem (pairPolyPtr (pa s out) j))
    (hg : g∈gamma2s) (hB : 1≤B) (hB' : B≤524288) :
    Paired.PairedLowReady c secret out low work g B s := by
  refine ⟨L.nwp hc,L.nwp hsecret,L.nwp hout,L.nwp hlow,L.nwp hwork,held,hfit,hsep,
    L.disj hc_out,L.disj hc_low,L.disj hc_work,L.disj hsecret_out,L.disj hsecret_low,L.disj hsecret_work,L.disj hout_low,L.disj hout_work,L.disj hlow_work,
    hprod,hdata,hg,hB,hB',?_,?_⟩
  · exact Covers.cons (L.cR hc) (Covers.cons (L.cR hsecret) (Covers.cons ht
      (Covers.cons (L.cR hout) (Covers.cons (L.cR hlow) (L.cR hwork)))))
  · exact Covers.cons (L.cW hwout) (Covers.cons (L.cW hwlow) (L.cW hwwork))

theorem pairedLowAt_layout {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State}
    (L : Lay S rbs wbs s) {c secret out low work : Ptr} {g B : Nat}
    (hc : inB (rbs++wbs) c 1024=true)
    (hsecret : inB (rbs++wbs) secret 2048=true)
    (hout : inB (rbs++wbs) out 2048=true)
    (hlow : inB (rbs++wbs) low 2048=true)
    (hwork : inB (rbs++wbs) work 2176=true)
    (h : Paired.PairedLowReady c secret out low work g B s) :
    WP isa (callAt "vg_mldsa_fused_pair_r0"
      (VG.Impl.MlDsa.AArch64.Optimized.Paired.selected .r0)
      (Paired.pairedLowArgs c secret out low work g B)) s fun t =>
      PPostB S s t [(out,2048),(low,2048),(work,2176)] ∧ t.gpr .x24=s.gpr .x24 ∧
      Paired.PairedLowPost g B s.mem t.mem (pa s c) (pa s secret) (pa s out) (pa s low) ((t.gpr .x0).setWidth 32) := by
  refine WP.mono (Paired.pairedLowAt_ok L.s64
    (ptr_ok (L.ptrBs hc)) (ptr_ok (L.ptrBs hsecret)) (ptr_ok (L.ptrBs hout))
    (ptr_ok (L.ptrBs hlow)) (ptr_ok (L.ptrBs hwork)) h) fun t ⟨hp,hv⟩ => ?_
  exact ⟨hp.b,hp.cs .x24 (by decide) (by decide),hv⟩

end VG.Proof.MlDsa.AArch64.Sign
