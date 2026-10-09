import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedHints
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedHintState
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedHintRow

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (sc seqR)
open VG.Proof.MlDsa.AArch64.Optimized

def optimizedHintChk (p : Params) (i : Nat) : Bool :=
  let wr := hintRowWrites i
  let wf := [(sc oONES,8)]
  kbChk p wr && famChk (sgR p) (sgW p) wr (yBase p) p.ℓ &&
  famChk (sgR p) (sgW p) wr (wBase p) p.k &&
  famChk (sgR p) (sgW p) wr (5+(i+1)) (p.k-(i+1)) &&
  famChk (sgR p) (sgW p) wr 5 i && keepB (sgR p) (sgW p) wr (sc oONES) 8 &&
  wr.all (fun w=>inB (sgW p) w.1 w.2) &&
  kbChk p wf && famChk (sgR p) (sgW p) wf (yBase p) p.ℓ &&
  famChk (sgR p) (sgW p) wf (wBase p) p.k &&
  famChk (sgR p) (sgW p) wf (5+(i+1)) (p.k-(i+1)) &&
  famChk (sgR p) (sgW p) wf 5 (i+1) &&
  inB (sgB p) (sc oONES) 8 && inB (sgW p) (sc oONES) 8 &&
  decide (p.γ₂∈gamma2s ∧ p.k≤8)

theorem optimizedHintChk_ok {p : Params} (hp : Ok3 p) : ∀i<p.k,optimizedHintChk p i=true := by
  rcases hp with rfl|rfl|rfl <;> decide

theorem optimizedHint_ok {p : Params} {S : Nat} {σ s : State} {t i : Nat}
    (hp : Ok3 p) (hi : i<p.k) (h : PositiveIH p S σ t i s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.hR p i) s (PositiveIH p S σ t (i+1)) := by
  have hc := optimizedHintChk_ok hp i hi
  simp only [optimizedHintChk,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨kr,zr⟩,hr⟩,lr⟩,fr⟩,orr⟩,wr⟩,kf⟩,zf⟩,hf⟩,lf⟩,ff⟩,ir⟩,iw⟩,hg,hk⟩ := hc
  obtain ⟨h,hflag⟩ := h
  have hl : SignedPolyIs s.mem (pa s (hP i))
      ((W'v p σ (p.ℓ*t) i).map fun r=>ofInt (lowBits p.γ₂ r)) (-(p.γ₂:Int)) p.γ₂ := by
    have hl := h.low 0 (by omega)
    simpa only [Nat.add_zero,R0v,W'v,VG.Proof.MlDsa.Sign.r0F] using hl
  have hh : NatPolyIs s.mem (pa s (wP p i)) (WHighv p σ (p.ℓ*t) i) := h.high i hi
  unfold Impl.MlDsa.AArch64.Sign.Optimized.hR
  refine WP.seq (WP.mono_syms (hintRow_ok hp hi ⟨h.b.l.st,h.b.l.k.d.roots⟩ h.b.c
    (h.b.l.k.d.t0 i hi) hl hh hg) fun a ⟨hpa,hroot,h24,hint,hret⟩ hsa => ?_)
  change HintIs a.mem (pa a (hP i)) 1 [Vector.zipWith _ (CT0v p σ (p.ℓ*t) i) (W'v p σ (p.ℓ*t) i)] at hint
  rw [hintRow_value] at hint
  change a.gpr .x0=BitVec.ofNat 64 (hintOnes [Vector.zipWith _ (CT0v p σ (p.ℓ*t) i) (W'v p σ (p.ℓ*t) i)]+
    if normRq [CT0v p σ (p.ℓ*t) i]<p.γ₂ then 4294967296 else 0) at hret
  rw [hintRow_value] at hret
  have ba := h.b.step hpa hsa kr wr
  have za := h.z.keep h.b.l.st.lay hpa zr
  have higha := h.high.keep h.b.l.st.lay hpa hr
  have lowshift : SignedFam s (5+(i+1)) (p.k-(i+1))
      (fun j=>R0v p σ (p.ℓ*t) (i+1+j)) (-(p.γ₂:Int)) p.γ₂ := by
    have hs := h.low.shift (by omega)
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,Nat.sub_sub] using hs
  have lowa := lowshift.keep h.b.l.st.lay hpa lr
  have hintsa := (HFam.keep h.b.l.st.lay hpa fr h.h).snoc hint
  have onesa := (h.b.l.st.lay.keepW hpa orr).trans h.ones
  have hbound : onesSum (Hv p σ (p.ℓ*t)) i+hintOnes [Hv p σ (p.ℓ*t) i]<2^32 := by
    have := onesSum_le (Hv p σ (p.ℓ*t)) i
    have := hintOnes_le (Hv p σ (p.ℓ*t) i)
    omega
  refine WP.mono_syms (hintFinish_semantic (S := S) a _ _ _ _ (ba.l.st.lay.inR ir)
    (ba.l.st.lay.inW iw) hbound onesa hret (h24.trans hflag)) fun b ⟨hpb,hmem,hflagb⟩ hsb => ?_
  refine ⟨⟨ba.step hpb hsb kf (by simpa using iw),za.keep ba.l.st.lay hpb zf,
    higha.keep ba.l.st.lay hpb hf,lowa.keep ba.l.st.lay hpb lf,
    HFam.keep ba.l.st.lay hpb ff hintsa,?_⟩,?_⟩
  · rw [hpb.pa (sc_bases _),hmem,Mem.readW_writeW_self64,onesSum_succ]
  · rw [hflagb]
    apply bit_congr
    exact ⟨fun ⟨⟨a,b⟩,c⟩=>⟨a,forall_lt_succ.mp ⟨b,c⟩⟩,
      fun ⟨a,b⟩=>⟨⟨a,(forall_lt_succ.mpr b).1⟩,(forall_lt_succ.mpr b).2⟩⟩

theorem optimizedHint_vector_ok {p : Params} {S : Nat} {σ s : State} {t : Nat}
    (hp : Ok3 p) (h : PositiveIH p S σ t 0 s) :
    WP isa (seqR (Impl.MlDsa.AArch64.Sign.Optimized.hR p) 0 p.k) s (PositiveIH p S σ t p.k) := by
  simpa only [Nat.zero_add] using seqR_ok (I := fun i s=>PositiveIH p S σ t i s)
    p.k 0 (fun i _ hi s h=>optimizedHint_ok hp (by omega) h) s h

end VG.Proof.MlDsa.AArch64.Sign
