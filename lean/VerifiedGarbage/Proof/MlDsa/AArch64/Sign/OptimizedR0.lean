import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedLowState

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
