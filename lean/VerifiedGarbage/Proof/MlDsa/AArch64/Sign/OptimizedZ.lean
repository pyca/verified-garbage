import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedResponseState
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedZCheck

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (sc)
open VG.Proof.MlDsa.AArch64.Optimized

def optimizedZChk (p : Params) (r : Nat) : Bool :=
  let wp := [(t1P,1024),(sc oPS,1024)]
  let wz := [(yP p r,1024)]
  inB (sgB p) (yP p r) 1024 && inB (sgB p) t1P 1024 &&
  inB (sgW p) (yP p r) 1024 && sepB (sgR p) (sgW p) (yP p r) 1024 t1P 1024 &&
  decide (1≤p.γ₁-p.β ∧ p.γ₁-p.β≤524288) &&
  zfam p wp r && famChk (sgR p) (sgW p) wp (yBase p+r) (p.ℓ-r) &&
  zfam p wz r && famChk (sgR p) (sgW p) wz (yBase p+(r+1)) (p.ℓ-(r+1)) &&
  zfam p [] (r+1) && famChk (sgR p) (sgW p) [] (yBase p+(r+1)) (p.ℓ-(r+1)) &&
  wp.all (fun w => inB (sgW p) w.1 w.2)

theorem optimizedZChk_ok {p : Params} (hp : Ok3 p) : ∀r<p.ℓ,optimizedZChk p r=true := by
  rcases hp with rfl | rfl | rfl <;> decide

theorem optimizedZ_ok {p : Params} {S : Nat} {σ s : State} {t r : Nat}
    (hp : Ok3 p) (hr : r<p.ℓ) (h : PositiveIZ p S σ t r s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.zR p r) s (PositiveIZ p S σ t (r+1)) := by
  have hc := optimizedZChk_ok hp r hr
  simp only [optimizedZChk,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hyr,hcr⟩,hyw⟩,hsep⟩,hb⟩,zp⟩,yp⟩,zz⟩,yz⟩,ze⟩,ye⟩,hwp⟩ := hc
  obtain ⟨h,hflag⟩ := h
  unfold Impl.MlDsa.AArch64.Sign.Optimized.zR
  refine WP.seq (WP.mono_syms (responseProduct_ok ⟨h.b.l.st,h.b.l.k.d.roots⟩
    (responseProductChk_z hp r hr) h.b.c (h.b.l.k.d.s1 r hr)) fun a ⟨hpa,h24a,hprod⟩ hsa => ?_)
  have ha := h.step hpa hsa zp yp hwp
  have hy : PolyIs a.mem (pa a (yP p r)) (Yv p σ (p.ℓ*t) r) := by
    have hv := ha.y 0 (by omega)
    simpa only [Nat.add_zero] using hv
  have hraw : RawPolyIs a.mem (pa a t1P)
      (nttInv (multiplyNTT (VG.Proof.MlDsa.Sign.chF (cV p σ (p.ℓ*t))) (S1v p σ r))) := by
    rw [hpa.pa (by decide)]; exact hprod
  have ready := addNormReady_layout ha.b.l.st.lay hyr hcr hyw hsep hy.1 hraw.1 hb.1 hb.2
  refine WP.seq (WP.mono_syms (addNormAt_field_layout ha.b.l.st.lay hyr hcr ready hy hraw)
    fun b ⟨hpb,h24b,hz,hret⟩ hsb => ?_)
  have hz' : SignedPl b (yBase p+r) (Zv p σ (p.ℓ*t) r) (-(q:Int)+1) ((q:Int)-1) := by
    change SignedPolyIs b.mem (pa b (yP p r)) _ _ _
    rw [hpb.pa (ha.b.l.st.lay.ptrBs hyr)]
    exact hz
  simp only [zfam,Bool.and_eq_true] at zz
  have hbstate : PositiveIZb p S σ t (r+1) b :=
    ⟨ha.b.step hpb hsb zz.1.1.1 (by simpa using hyw),
      (ha.z.keep ha.b.l.st.lay hpb zz.1.1.2).snoc hz',
      (ha.y.shift hr).keep ha.b.l.st.lay hpb yz,
      ha.w.keep ha.b.l.st.lay hpb zz.1.2,(ha.b.l.st.lay.keepW hpb zz.2).trans ha.ones⟩
  refine WP.mono_syms (and24_ok b) fun c ⟨hkc,hflagc⟩ hsc => ?_
  have hpc : PPostB S b c [] := postB24 hkc []
  refine ⟨hbstate.step hpc hsc ze ye (by simp),?_⟩
  rw [hflagc,bit_and (h24b.trans (h24a.trans hflag)) hret]
  exact bit_congr forall_lt_succ

/-- Every z polynomial is processed before the next rejection-check phase. -/
theorem optimizedZ_vector_ok {p : Params} {S : Nat} {σ s : State} {t : Nat}
    (hp : Ok3 p) (h : PositiveIZ p S σ t 0 s) :
    WP isa (VG.Impl.MlDsa.AArch64.Call.seqR (Impl.MlDsa.AArch64.Sign.Optimized.zR p) 0 p.ℓ)
      s (PositiveIZ p S σ t p.ℓ) := by
  simpa only [Nat.zero_add] using seqR_ok (I := fun r s => PositiveIZ p S σ t r s)
    p.ℓ 0 (fun r _ hr s h => optimizedZ_ok hp (by omega) h) s h

end VG.Proof.MlDsa.AArch64.Sign
