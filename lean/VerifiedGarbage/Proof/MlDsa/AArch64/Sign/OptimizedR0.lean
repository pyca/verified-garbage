module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedLowState
public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedLow
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRoots
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Representation
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowCall

import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Residue
import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Arith
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowMath
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Entry

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Optimized/ResponseLowField.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

theorem responseDifference_poly (m : Mem) (w cs : Addr) {i : Nat} (hi : i<n) :
    responseDifference m w cs i=(sub (polyAt m w) (signedPolyAt m cs))[i]! := by
  rw [responseDifference,ofInt_sub,sub_get _ _ hi,polyAt_get _ _ hi]
  have hn (v : Nat) : ofInt (v:Int)=ofNat v := by
    apply Fin.ext
    change ((v:Int) % (q:Int)).toNat%q=v%q
    rw [← Int.natCast_emod,Int.toNat_natCast,Nat.mod_mod]
  rw [hn,getElem!_eq _ hi]
  simp only [signedPolyAt,Vector.getElem_ofFn]

theorem responseLowPass_poly (m : Mem) (w cs : Addr) (g B : Nat) :
    responseLowPass m w cs g B ↔ normRq [(sub (polyAt m w) (signedPolyAt m cs)).map
      (fun c=>ofInt (lowBits g c))]<B := by
  rw [VG.Proof.MlDsa.Round.normRq_lt]
  apply forall_congr'; intro i
  apply forall_congr'; intro hi
  rw [responseDifference_poly _ _ _ hi,
    getElem!_eq ((sub (polyAt m w) (signedPolyAt m cs)).map (fun c=>ofInt (lowBits g c))) hi,
    Vector.getElem_map,getElem!_eq _ hi]

theorem SubLowNormPost.field {g B : Nat} {m m' : Mem} {w cs low : Addr} {r : BitVec 32} {f h : Poly}
    (hp : SubLowNormPost g B m m' w cs low r) (hg : VG.Proof.MlDsa.AArch64.Round.IsG g)
    (hf : PolyIs m w f) (hh : RawPolyIs m cs h) :
    NatPolyIs m' w ((sub f h).map fun c=>(highBits g c).toNat) ∧
    SignedPolyIs m' low ((sub f h).map fun c=>ofInt (lowBits g c)) (-(g:Int)) g ∧
    r=if normRq [((sub f h).map fun c=>ofInt (lowBits g c))]<B then 1 else 0 := by
  have he (i : Nat) (hi : i<n) : responseDifference m w cs i=(sub f h)[i]! := by
    rw [responseDifference_poly _ _ _ hi,hf.2,hh.2]
  refine ⟨?_,⟨?_,?_⟩,?_⟩
  · apply Vector.ext
    intro i hi
    simp only [natPolyAt,Vector.getElem_ofFn,Vector.getElem_map]
    rw [hp.1 i hi,he i hi,getElem!_eq _ hi]
  · intro i hi
    rw [hp.2.1 i hi]
    exact lowBits_bounds hg _
  · intro i hi
    rw [hp.2.1 i hi,he i hi,
      getElem!_eq ((sub f h).map (fun c=>ofInt (lowBits g c))) hi,Vector.getElem_map,getElem!_eq _ hi]
  · rw [hp.2.2]
    have hiff := responseLowPass_poly m w cs g B
    rw [hf.2,hh.2] at hiff
    simp only [hiff]

end VG.Proof.MlDsa.AArch64.Optimized.Response
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Sign/OptimizedLowCheck.lean`, which only this module imported.
section

@[expose] public section

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
end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (sc)
open VG.Proof.MlDsa.AArch64.Optimized

def optimizedR0Chk (p : Params) (i : Nat) : Bool :=
  let wp := [(t1P,1024),(sc oPS,1024)]
  let wr := [(wP p i,1024),(hP i,1024)]
  subLowNormChk p i && decide (p.γ₂∈gamma2s ∧ 1≤p.γ₂-p.β ∧ p.γ₂-p.β≤524288) &&
  positiveRfam p wp i && famChk (sgR p) (sgW p) wp (wBase p+i) (p.k-i) &&
  positiveRfam p wr i && famChk (sgR p) (sgW p) wr (wBase p+(i+1)) (p.k-(i+1)) &&
  positiveRfam p [] (i+1) && famChk (sgR p) (sgW p) [] (wBase p+(i+1)) (p.k-(i+1)) &&
  wp.all (fun w=>inB (sgW p) w.1 w.2)

theorem optimizedR0Chk_ok {p : Params} (hp : Ok3 p) : ∀i<p.k,optimizedR0Chk p i=true := by
  rcases hp with rfl|rfl|rfl <;> decide

theorem optimizedR0_ok {p : Params} {S : Nat} {σ s : State} {t i : Nat}
    (hp : Ok3 p) (hi : i<p.k) (h : PositiveIR p S σ t i s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.r0R p i) s (PositiveIR p S σ t (i+1)) := by
  have hc := optimizedR0Chk_ok hp i hi
  simp only [optimizedR0Chk,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨cl,hgb⟩,rp⟩,wp⟩,rr⟩,wr⟩,re⟩,we⟩,hwp⟩ := hc
  simp only [subLowNormChk,Bool.and_eq_true] at cl
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hwr,hcr⟩,hlr⟩,hww⟩,hwl⟩,hwc⟩,hwo⟩,hco⟩,_⟩ := cl
  obtain ⟨h,hflag⟩ := h
  unfold Impl.MlDsa.AArch64.Sign.Optimized.r0R
  refine WP.seq (WP.mono_syms (responseProduct_ok ⟨h.b.l.st,h.b.l.k.d.roots⟩
    (responseProductChk_r0 hp i hi) h.b.c (h.b.l.k.d.s2 i hi)) fun a ⟨hpa,h24a,hprod⟩ hsa => ?_)
  have ha := h.step hpa hsa rp wp hwp
  have hw : PolyIs a.mem (pa a (wP p i)) (Wv p σ (p.ℓ*t) i) := by
    have hv := ha.w 0 (by omega)
    simpa only [Nat.add_zero] using hv
  have hraw : RawPolyIs a.mem (pa a t1P) (nttInv (multiplyNTT
      (VG.Proof.MlDsa.Sign.chF (cV p σ (p.ℓ*t))) (S2v p σ i))) := by
    rw [hpa.pa (by decide)]; exact hprod
  have ready := subLowNormReady_layout ha.b.l.st.lay hwr hcr hlr hww hwl hwc hwo hco
    hw.1 hraw.1 hgb.1 hgb.2.1 hgb.2.2
  refine WP.seq (WP.mono_syms (subLowNormAt_field_layout ha.b.l.st.lay hwr hcr hlr ready hw hraw)
    fun b ⟨hpb,h24b,hhigh,hlow,hret⟩ hsb => ?_)
  have high' : NatPl b (wBase p+i) (WHighv p σ (p.ℓ*t) i) := by
    change NatPolyIs b.mem (pa b (wP p i)) _
    rw [hpb.pa (ha.b.l.st.lay.ptrBs hwr)]
    exact hhigh
  have low' : SignedPl b (5+i) (R0v p σ (p.ℓ*t) i) (-(p.γ₂:Int)) p.γ₂ := by
    change SignedPolyIs b.mem (pa b (hP i)) _ _ _
    rw [hpb.pa (ha.b.l.st.lay.ptrBs hlr)]
    exact hlow
  simp only [positiveRfam,Bool.and_eq_true] at rr
  have hbstate : PositiveIRb p S σ t (i+1) b :=
    ⟨ha.b.step hpb hsb rr.1.1.1.1 (by simpa using And.intro hww hwl),
      ha.z.keep ha.b.l.st.lay hpb rr.1.1.1.2,
      (ha.high.keep ha.b.l.st.lay hpb rr.1.1.2).snoc high',
      (ha.low.keep ha.b.l.st.lay hpb rr.1.2).snoc low',
      (ha.w.shift hi).keep ha.b.l.st.lay hpb wr,(ha.b.l.st.lay.keepW hpb rr.2).trans ha.ones⟩
  refine WP.mono_syms (and24_ok b) fun c ⟨hkc,hflagc⟩ hsc => ?_
  have hpc : PPostB S b c [] := postB24 hkc []
  refine ⟨hbstate.step hpc hsc re we (by simp),?_⟩
  rw [hflagc,bit_and (h24b.trans (h24a.trans hflag)) hret]
  exact bit_congr ⟨fun ⟨⟨a,b⟩,c⟩=>⟨a,forall_lt_succ.mp ⟨b,c⟩⟩,
    fun ⟨a,b⟩=>⟨⟨a,(forall_lt_succ.mpr b).1⟩,(forall_lt_succ.mpr b).2⟩⟩


/-- The whole r0 vector runs before the hint phase or rejection branch. -/
theorem optimizedR0_vector_ok {p : Params} {S : Nat} {σ s : State} {t : Nat}
    (hp : Ok3 p) (h : PositiveIR p S σ t 0 s) :
    WP isa (VG.Impl.MlDsa.AArch64.Call.seqR (Impl.MlDsa.AArch64.Sign.Optimized.r0R p) 0 p.k)
      s (PositiveIR p S σ t p.k) := by
  simpa only [Nat.zero_add] using seqR_ok (I := fun i s=>PositiveIR p S σ t i s)
    p.k 0 (fun i _ hi s h=>optimizedR0_ok hp (by omega) h) s h

end VG.Proof.MlDsa.AArch64.Sign
