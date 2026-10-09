import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedCalls
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRoots
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintCallTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintDecompose

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Proof.MlDsa.AArch64.Optimized

theorem hintNormReady_layout {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State}
    (L : Lay S rbs wbs s) {low ct high : Ptr} {g : Nat}
    (hl : inB (rbs++wbs) low 1024=true) (hc : inB (rbs++wbs) ct 1024=true)
    (hh : inB (rbs++wbs) high 1024=true) (hw : inB wbs low 1024=true)
    (hd : sepB rbs wbs low 1024 ct 1024=true) (he : sepB rbs wbs low 1024 high 1024=true)
    (hg : g∈gamma2s) (hraw : RawReduced s.mem (pa s ct))
    (hparts : ResponseDecomposed s.mem (pa s low) (pa s high) g) :
    Response.HintNormReady low ct high g s := by
  exact ⟨L.nwp hl,L.nwp hc,L.nwp hh,L.disj hd,L.disj he,hg,hraw,hparts,
    Covers.cons (L.cR hc) (Covers.cons (L.cR hh) (L.cR hl)),L.cW hw⟩

theorem hintNormAt_layout {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State}
    (L : Lay S rbs wbs s) {low ct high : Ptr} {g : Nat}
    (hl : inB (rbs++wbs) low 1024=true) (hc : inB (rbs++wbs) ct 1024=true)
    (hh : inB (rbs++wbs) high 1024=true) (h : Response.HintNormReady low ct high g s) :
    WP isa (callAt "vg_mldsa_signed_hint_norm" VG.Impl.MlDsa.AArch64.Optimized.Response.hintNorm
      (Response.hintNormArgs low ct high g)) s fun t =>
      PPostB S s t [(low,1024)] ∧ t.gpr .x24=s.gpr .x24 ∧
      Response.HintNormPost g s.mem t.mem (pa s low) (pa s ct) (pa s high) (t.gpr .x0) := by
  refine WP.mono (Response.hintNormAt_ok L.s64 (ptr_ok (L.ptrBs hl)) (ptr_ok (L.ptrBs hc))
    (ptr_ok (L.ptrBs hh)) h) fun t ⟨hp,hv⟩ => ?_
  exact ⟨hp.b,hp.cs .x24 (by decide) (by decide),hv⟩

theorem hintNormAt_field_layout {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State}
    (L : Lay S rbs wbs s) {low ct high : Ptr} {g : Nat} {f c : Poly}
    (hl : inB (rbs++wbs) low 1024=true) (hc : inB (rbs++wbs) ct 1024=true)
    (hh : inB (rbs++wbs) high 1024=true) (hr : Response.HintNormReady low ct high g s)
    (hlo : SignedPolyIs s.mem (pa s low) (f.map fun r=>ofInt (lowBits g r)) (-(g:Int)) g)
    (hhi : NatPolyIs s.mem (pa s high) (f.map fun r=>(highBits g r).toNat))
    (hct : RawPolyIs s.mem (pa s ct) c) :
    WP isa (callAt "vg_mldsa_signed_hint_norm" VG.Impl.MlDsa.AArch64.Optimized.Response.hintNorm
      (Response.hintNormArgs low ct high g)) s fun t =>
      PPostB S s t [(low,1024)] ∧ t.gpr .x24=s.gpr .x24 ∧
      HintIs t.mem (pa s low) 1 [Vector.zipWith (fun ci fi=>makeHint g (-ci) (fi+ci)) c f] ∧
      t.gpr .x0=BitVec.ofNat 64 (hintOnes [Vector.zipWith (fun ci fi=>makeHint g (-ci) (fi+ci)) c f]+
        if normRq [c]<g then 4294967296 else 0) := by
  refine WP.mono (hintNormAt_layout L hl hc hh hr) fun t ⟨hp,h24,hv⟩ => ?_
  exact ⟨hp,h24,hv.field (VG.Proof.MlDsa.AArch64.Round.isG_of_mem hr.gamma) hlo hhi hct⟩

open VG.Impl.MlDsa.AArch64.Sign

def hintNormChk (p : Params) (i : Nat) : Bool :=
  inB (sgR p++sgW p) (hP i) 1024 && inB (sgR p++sgW p) t1P 1024 &&
  inB (sgR p++sgW p) (wP p i) 1024 && inB (sgW p) (hP i) 1024 &&
  sepB (sgR p) (sgW p) (hP i) 1024 t1P 1024 &&
  sepB (sgR p) (sgW p) (hP i) 1024 (wP p i) 1024 && stChk p [(hP i,1024)]

theorem hintNormChk_ok {p : Params} (hp : Ok3 p) : ∀i<p.k,hintNormChk p i=true := by
  rcases hp with rfl|rfl|rfl <;> decide

theorem hintNorm_rooted {p : Params} {S : Nat} {σ s : State} {i : Nat} {f c : Poly}
    (hc : hintNormChk p i=true) (hs : RootedSt p S σ s)
    (hl : SignedPolyIs s.mem (pa s (hP i)) (f.map fun r=>ofInt (lowBits p.γ₂ r)) (-(p.γ₂:Int)) p.γ₂)
    (hh : NatPolyIs s.mem (pa s (wP p i)) (f.map fun r=>(highBits p.γ₂ r).toNat))
    (hct : RawPolyIs s.mem (pa s t1P) c) (hg : p.γ₂∈gamma2s) :
    WP isa (callAt "vg_mldsa_signed_hint_norm" VG.Impl.MlDsa.AArch64.Optimized.Response.hintNorm
      (Response.hintNormArgs (hP i) t1P (wP p i) p.γ₂)) s fun t =>
      RootedSt p S σ t ∧ t.gpr .x24=s.gpr .x24 ∧
      HintIs t.mem (pa t (hP i)) 1 [Vector.zipWith (fun ci fi=>makeHint p.γ₂ (-ci) (fi+ci)) c f] ∧
      t.gpr .x0=BitVec.ofNat 64 (hintOnes [Vector.zipWith (fun ci fi=>makeHint p.γ₂ (-ci) (fi+ci)) c f]+
        if normRq [c]<p.γ₂ then 4294967296 else 0) := by
  simp only [hintNormChk,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨hlr,hcr⟩,hhr⟩,hlw⟩,hlc⟩,hlh⟩,hst⟩ := hc
  have hg' := VG.Proof.MlDsa.AArch64.Round.isG_of_mem hg
  have hparts := Response.responseDecomposed_parts hg' f (Response.hintLow_exact hg' hl) (Response.hintHigh_exact hh)
  have hr := hintNormReady_layout hs.1.lay hlr hcr hhr hlw hlc hlh hg hct.1 hparts
  refine WP.mono_syms (hintNormAt_field_layout hs.1.lay hlr hcr hhr hr hl hh hct)
    fun t ⟨hp,h24,hout,hret⟩ hy => ?_
  refine ⟨hs.step hp hy hst (by simpa using hlw),h24,?_,hret⟩
  rw [hp.pa (hs.1.lay.ptrBs hlr)]
  exact hout

theorem hintNorm_rooted_frame {p : Params} {S : Nat} {σ s : State} {i : Nat} {f c : Poly}
    (hc : hintNormChk p i=true) (hs : RootedSt p S σ s)
    (hl : SignedPolyIs s.mem (pa s (hP i)) (f.map fun r=>ofInt (lowBits p.γ₂ r)) (-(p.γ₂:Int)) p.γ₂)
    (hh : NatPolyIs s.mem (pa s (wP p i)) (f.map fun r=>(highBits p.γ₂ r).toNat))
    (hct : RawPolyIs s.mem (pa s t1P) c) (hg : p.γ₂∈gamma2s) :
    WP isa (callAt "vg_mldsa_signed_hint_norm" VG.Impl.MlDsa.AArch64.Optimized.Response.hintNorm
      (Response.hintNormArgs (hP i) t1P (wP p i) p.γ₂)) s fun t =>
      PPostB S s t [(hP i,1024)] ∧ RootedSt p S σ t ∧ t.gpr .x24=s.gpr .x24 ∧
      HintIs t.mem (pa t (hP i)) 1 [Vector.zipWith (fun ci fi=>makeHint p.γ₂ (-ci) (fi+ci)) c f] ∧
      t.gpr .x0=BitVec.ofNat 64 (hintOnes [Vector.zipWith (fun ci fi=>makeHint p.γ₂ (-ci) (fi+ci)) c f]+
        if normRq [c]<p.γ₂ then 4294967296 else 0) := by
  simp only [hintNormChk,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨hlr,hcr⟩,hhr⟩,hlw⟩,hlc⟩,hlh⟩,hst⟩ := hc
  have hg' := VG.Proof.MlDsa.AArch64.Round.isG_of_mem hg
  have hparts := Response.responseDecomposed_parts hg' f (Response.hintLow_exact hg' hl) (Response.hintHigh_exact hh)
  have hr := hintNormReady_layout hs.1.lay hlr hcr hhr hlw hlc hlh hg hct.1 hparts
  refine WP.mono_syms (hintNormAt_field_layout hs.1.lay hlr hcr hhr hr hl hh hct)
    fun t ⟨hp,h24,hout,hret⟩ hy => ?_
  refine ⟨hp,hs.step hp hy hst (by simpa using hlw),h24,?_,hret⟩
  rw [hp.pa (hs.1.lay.ptrBs hlr)]
  exact hout

end VG.Proof.MlDsa.AArch64.Sign
