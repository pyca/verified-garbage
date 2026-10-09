import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedCalls
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseZCallTiming

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Proof.MlDsa.AArch64.Optimized

/-- The response remains signed through all strict rejection checks. -/
theorem centered_signed {m : Mem} {p : Addr} {f : Poly}
    (hb : CenteredReduced m p) (hv : signedPolyAt m p=f) :
    SignedPolyIs m p f (-(q:Int)+1) ((q:Int)-1) := by
  refine ⟨?_,?_⟩
  · intro i hi
    have := hb i hi
    omega
  · intro i hi
    rw [← hv,VG.Proof.MlDsa.Arith.getElem!_eq _ hi]
    simp only [signedPolyAt,Vector.getElem_ofFn]

theorem addNormReady_layout {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State}
    (L : Lay S rbs wbs s) {y cs : Ptr} {B : Nat}
    (hy : inB (rbs++wbs) y 1024=true) (hc : inB (rbs++wbs) cs 1024=true)
    (hwy : inB wbs y 1024=true) (hd : sepB rbs wbs y 1024 cs 1024=true)
    (ha : Reduced s.mem (pa s y)) (hb : RawReduced s.mem (pa s cs))
    (hB : 1≤B) (hB' : B≤524288) : Response.AddNormReady y cs B s := by
  exact ⟨L.nwp hy,L.nwp hc,L.disj hd,ha,hb,hB,hB',Covers.cons (L.cR hc) (L.cR hy),L.cW hwy⟩

theorem addNormAt_layout {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State}
    (L : Lay S rbs wbs s) {y cs : Ptr} {B : Nat}
    (hy : inB (rbs++wbs) y 1024=true) (hc : inB (rbs++wbs) cs 1024=true)
    (h : Response.AddNormReady y cs B s) :
    WP isa (callAt "vg_mldsa_signed_add_norm" VG.Impl.MlDsa.AArch64.Optimized.Response.addNorm
      (Response.addNormArgs y cs B)) s fun t =>
      PPostB S s t [(y,1024)] ∧ t.gpr .x24=s.gpr .x24 ∧
      SignedPolyIs t.mem (pa s y) (add (polyAt s.mem (pa s y)) (signedPolyAt s.mem (pa s cs)))
        (-(q:Int)+1) ((q:Int)-1) ∧
      (t.gpr .x0).setWidth 32=if normRq [add (polyAt s.mem (pa s y)) (signedPolyAt s.mem (pa s cs))]<B then 1 else 0 := by
  refine WP.mono (Response.addNormAt_ok L.s64 (ptr_ok (L.ptrBs hy)) (ptr_ok (L.ptrBs hc)) h)
    fun t ⟨hp,hcenter,hpoly,hret⟩ => ?_
  exact ⟨hp.b,hp.cs .x24 (by decide) (by decide),centered_signed hcenter hpoly,hret⟩

theorem addNormAt_field_layout {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State}
    (L : Lay S rbs wbs s) {y cs : Ptr} {B : Nat} {f g : Poly}
    (hy : inB (rbs++wbs) y 1024=true) (hc : inB (rbs++wbs) cs 1024=true)
    (h : Response.AddNormReady y cs B s) (hf : PolyIs s.mem (pa s y) f) (hg : RawPolyIs s.mem (pa s cs) g) :
    WP isa (callAt "vg_mldsa_signed_add_norm" VG.Impl.MlDsa.AArch64.Optimized.Response.addNorm
      (Response.addNormArgs y cs B)) s fun t =>
      PPostB S s t [(y,1024)] ∧ t.gpr .x24=s.gpr .x24 ∧
      SignedPolyIs t.mem (pa s y) (add f g) (-(q:Int)+1) ((q:Int)-1) ∧
      (t.gpr .x0).setWidth 32=if normRq [add f g]<B then 1 else 0 := by
  refine WP.mono (addNormAt_layout L hy hc h) fun t ⟨hp,h24,hv,hr⟩ => ?_
  exact ⟨hp,h24,by simpa only [hf.2,hg.2] using hv,by simpa only [hf.2,hg.2] using hr⟩

end VG.Proof.MlDsa.AArch64.Sign
