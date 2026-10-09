import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedCalls
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRoots
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowCallTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowField

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Proof.MlDsa.AArch64.Optimized

/-- Construct the fused r0 check's independent canonical/raw input contract
from the signer's existing disjoint scratch layout. -/
theorem subLowNormReady_layout {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State}
    (L : Lay S rbs wbs s) {w cs low : Ptr} {g B : Nat}
    (hw : inB (rbs++wbs) w 1024=true) (hc : inB (rbs++wbs) cs 1024=true)
    (hl : inB (rbs++wbs) low 1024=true)
    (hww : inB wbs w 1024=true) (hwl : inB wbs low 1024=true)
    (hwc : sepB rbs wbs w 1024 cs 1024=true)
    (hwo : sepB rbs wbs w 1024 low 1024=true)
    (hco : sepB rbs wbs cs 1024 low 1024=true)
    (hcan : Reduced s.mem (pa s w)) (hraw : RawReduced s.mem (pa s cs))
    (hg : g∈gamma2s) (hB : 1≤B) (hB' : B≤524288) :
    Response.SubLowNormReady w cs low g B s := by
  refine ⟨L.nwp hw,L.nwp hc,L.nwp hl,L.disj hwc,L.disj hwo,L.disj hco,hcan,hraw,hg,hB,hB',?_,?_⟩
  · exact Covers.cons (L.cR hc) (Covers.cons (L.cR hw) (L.cR hl))
  · exact Covers.cons (L.cW hww) (L.cW hwl)

theorem subLowNormAt_layout {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State}
    (L : Lay S rbs wbs s) {w cs low : Ptr} {g B : Nat}
    (hw : inB (rbs++wbs) w 1024=true) (hc : inB (rbs++wbs) cs 1024=true)
    (hl : inB (rbs++wbs) low 1024=true)
    (h : Response.SubLowNormReady w cs low g B s) :
    WP isa (callAt "vg_mldsa_signed_sub_low_norm"
      VG.Impl.MlDsa.AArch64.Optimized.Response.subLowNorm (Response.subLowNormArgs w cs low g B)) s fun t =>
      PPostB S s t [(w,1024),(low,1024)] ∧ t.gpr .x24=s.gpr .x24 ∧
      Response.SubLowNormPost g B s.mem t.mem (pa s w) (pa s cs) (pa s low) ((t.gpr .x0).setWidth 32) := by
  refine WP.mono (Response.subLowNormAt_ok L.s64 (ptr_ok (L.ptrBs hw)) (ptr_ok (L.ptrBs hc))
    (ptr_ok (L.ptrBs hl)) h) fun t ⟨hp,hv⟩ => ?_
  exact ⟨hp.b,hp.cs .x24 (by decide) (by decide),hv⟩


theorem subLowNormAt_field_layout {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State}
    (L : Lay S rbs wbs s) {w cs low : Ptr} {g B : Nat} {f h : Poly}
    (hw : inB (rbs++wbs) w 1024=true) (hc : inB (rbs++wbs) cs 1024=true)
    (hl : inB (rbs++wbs) low 1024=true)
    (hr : Response.SubLowNormReady w cs low g B s)
    (hf : PolyIs s.mem (pa s w) f) (hh : RawPolyIs s.mem (pa s cs) h) :
    WP isa (callAt "vg_mldsa_signed_sub_low_norm"
      VG.Impl.MlDsa.AArch64.Optimized.Response.subLowNorm (Response.subLowNormArgs w cs low g B)) s fun t =>
      PPostB S s t [(w,1024),(low,1024)] ∧ t.gpr .x24=s.gpr .x24 ∧
      NatPolyIs t.mem (pa s w) ((sub f h).map fun c=>(highBits g c).toNat) ∧
      SignedPolyIs t.mem (pa s low) ((sub f h).map fun c=>ofInt (lowBits g c)) (-(g:Int)) g ∧
      (t.gpr .x0).setWidth 32=if normRq [((sub f h).map fun c=>ofInt (lowBits g c))]<B then 1 else 0 := by
  refine WP.mono (subLowNormAt_layout L hw hc hl hr) fun t ⟨hp,h24,hpost⟩ => ?_
  exact ⟨hp,h24,hpost.field (VG.Proof.MlDsa.AArch64.Round.isG_of_mem hr.gamma) hf hh⟩

open VG.Impl.MlDsa.AArch64.Sign

def subLowNormChk (p : Params) (i : Nat) : Bool :=
  inB (sgR p++sgW p) (wP p i) 1024 && inB (sgR p++sgW p) t1P 1024 &&
  inB (sgR p++sgW p) (hP i) 1024 && inB (sgW p) (wP p i) 1024 && inB (sgW p) (hP i) 1024 &&
  sepB (sgR p) (sgW p) (wP p i) 1024 t1P 1024 &&
  sepB (sgR p) (sgW p) (wP p i) 1024 (hP i) 1024 &&
  sepB (sgR p) (sgW p) t1P 1024 (hP i) 1024 && stChk p [(wP p i,1024),(hP i,1024)]

theorem subLowNormChk_ok {p : Params} (hp : Ok3 p) : ∀i<p.k,subLowNormChk p i=true := by
  rcases hp with rfl|rfl|rfl <;> decide

theorem subLowNorm_rooted {p : Params} {S : Nat} {σ s : State} {i : Nat}
    (hc : subLowNormChk p i=true) (hs : RootedSt p S σ s)
    (hcan : Reduced s.mem (pa s (wP p i))) (hraw : RawReduced s.mem (pa s t1P))
    (hg : p.γ₂∈gamma2s) (hB : 1≤p.γ₂-p.β) (hB' : p.γ₂-p.β≤524288) :
    WP isa (callAt "vg_mldsa_signed_sub_low_norm"
      VG.Impl.MlDsa.AArch64.Optimized.Response.subLowNorm
      (Response.subLowNormArgs (wP p i) t1P (hP i) p.γ₂ (p.γ₂-p.β))) s fun t =>
      RootedSt p S σ t ∧ t.gpr .x24=s.gpr .x24 ∧
      Response.SubLowNormPost p.γ₂ (p.γ₂-p.β) s.mem t.mem (pa t (wP p i)) (pa t t1P) (pa t (hP i))
        ((t.gpr .x0).setWidth 32) := by
  simp only [subLowNormChk,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hw,hr⟩,hl⟩,hww⟩,hwl⟩,hwc⟩,hwo⟩,hco⟩,hst⟩ := hc
  have hready := subLowNormReady_layout hs.1.lay hw hr hl hww hwl hwc hwo hco hcan hraw hg hB hB'
  refine WP.mono_syms (subLowNormAt_layout hs.1.lay hw hr hl hready) fun t ⟨hp,h24,hv⟩ hy => ?_
  refine ⟨hs.step hp hy hst (by simpa using And.intro hww hwl),h24,?_⟩
  rw [hp.pa (hs.1.lay.ptrBs hw),hp.pa (hs.1.lay.ptrBs hr),hp.pa (hs.1.lay.ptrBs hl)]
  exact hv

end VG.Proof.MlDsa.AArch64.Sign
