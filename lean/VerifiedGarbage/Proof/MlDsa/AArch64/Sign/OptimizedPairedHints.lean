import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedHintRow
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedHints

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (sc seqR)
open VG.Proof.MlDsa.AArch64.Optimized

def pairedHintChk (p : Params) (i : Nat) : Bool :=
  let wr := pairedHintWrites i
  let wf := [(sc oONES,8)]
  kbChk p wr && famChk (sgR p) (sgW p) wr (yBase p) p.ℓ &&
  famChk (sgR p) (sgW p) wr (wBase p) p.k &&
  famChk (sgR p) (sgW p) wr (5+(i+2)) (p.k-(i+2)) &&
  famChk (sgR p) (sgW p) wr 5 i && keepB (sgR p) (sgW p) wr (sc oONES) 8 &&
  wr.all (fun w=>inB (sgW p) w.1 w.2) &&
  kbChk p wf && famChk (sgR p) (sgW p) wf (yBase p) p.ℓ &&
  famChk (sgR p) (sgW p) wf (wBase p) p.k &&
  famChk (sgR p) (sgW p) wf (5+(i+2)) (p.k-(i+2)) &&
  famChk (sgR p) (sgW p) wf 5 (i+2) &&
  inB (sgB p) (sc oONES) 8 && inB (sgW p) (sc oONES) 8 &&
  decide (p.γ₂∈gamma2s ∧ 0<p.γ₂ ∧ p.k≤8)

theorem pairedHintChk_ok {p : Params} (hp : Ok3 p) : ∀i<p.k,i+1<p.k → pairedHintChk p i=true := by
  rcases hp with rfl|rfl|rfl <;> decide

theorem onesSum_pair (f : Nat → Vector Bool n) (i : Nat) :
    onesSum f i+hintOnes ((List.range 2).map fun j=>f (i+j))=onesSum f (i+2) := by
  rw [hintOnes_pair]
  simp only [Nat.add_zero]
  rw [show i+2=(i+1)+1 by omega,onesSum_succ,onesSum_succ]
  omega

theorem optimizedHint_pair_ok {p : Params} {S : Nat} {σ s : State} {t i : Nat}
    (hp : Ok3 p) (hi : i+1<p.k) (roots : PairedRoots S s) (h : PositiveIH p S σ t i s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.hintPair p i) s fun u =>
      PositiveIH p S σ t (i+2) u ∧ PairedRoots S u := by
  have hc := pairedHintChk_ok hp i (by omega) hi
  simp only [pairedHintChk,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨kr,zr⟩,hr⟩,lr⟩,fr⟩,orr⟩,wr⟩,kf⟩,zf⟩,hf⟩,lf⟩,ff⟩,ir⟩,iw⟩,hg,hgpos,hk⟩ := hc
  unfold Impl.MlDsa.AArch64.Sign.Optimized.hintPair
  refine WP.seq (WP.mono_syms (pairedHintRow_ok hp hi roots h) fun a ⟨hpa,h24,hint,hret⟩ hsa => ?_)
  obtain ⟨h,hflag⟩ := h
  have ra := roots.step_layout h.b.l.st.lay hpa hsa wr
  have ba := h.b.step hpa hsa kr wr
  have za := h.z.keep h.b.l.st.lay hpa zr
  have higha := h.high.keep h.b.l.st.lay hpa hr
  have lowshift : SignedFam s (5+(i+2)) (p.k-(i+2))
      (fun j=>R0v p σ (p.ℓ*t) (i+2+j)) (-(p.γ₂:Int)) p.γ₂ := by
    intro j hj
    show SignedPl s (5+(i+2)+j) (R0v p σ (p.ℓ*t) (i+2+j)) _ _
    rw [show 5+(i+2)+j=5+i+(j+2) by omega,show i+2+j=i+(j+2) by omega]
    exact h.low (j+2) (by omega)
  have lowa := lowshift.keep h.b.l.st.lay hpa lr
  have hints : ∀j<2,HintIs a.mem (pa a (hP (i+j))) 1 [Hv p σ (p.ℓ*t) (i+j)] := by
    intro j hj
    have hv := hintIs_pair hint hj
    rw [paired_pS_addr] at hv
    rw [hpa.pa (pS_bases _)]
    simpa only [Nat.add_assoc] using hv
  have hintsa : HFam a 5 (i+2) (Hv p σ (p.ℓ*t)) := by
    have old := HFam.keep h.b.l.st.lay hpa fr h.h
    have h0 := hints 0 (by decide)
    have h1 := hints 1 (by decide)
    simpa only [Nat.add_zero,Nat.add_assoc] using (old.snoc (by simpa only [Nat.add_zero] using h0)).snoc h1
  have onesa := (h.b.l.st.lay.keepW hpa orr).trans h.ones
  have hbound : onesSum (Hv p σ (p.ℓ*t)) i+hintOnes ((List.range 2).map fun j=>Hv p σ (p.ℓ*t) (i+j))<2^32 := by
    rw [onesSum_pair]
    have := onesSum_le (Hv p σ (p.ℓ*t)) (i+2)
    omega
  refine WP.mono_syms (hintFinish_semantic (S:=S) a _ _ _ _ (ba.l.st.lay.inR ir)
    (ba.l.st.lay.inW iw) hbound onesa hret (h24.trans hflag)) fun b ⟨hpb,hmem,hflagb⟩ hsb => ?_
  have rb := ra.step_layout ba.l.st.lay hpb hsb (by simpa using iw)
  refine ⟨⟨⟨ba.step hpb hsb kf (by simpa using iw),za.keep ba.l.st.lay hpb zf,
    higha.keep ba.l.st.lay hpb hf,lowa.keep ba.l.st.lay hpb lf,
    HFam.keep ba.l.st.lay hpb ff hintsa,?_⟩,?_⟩,rb⟩
  · rw [hpb.pa (sc_bases _),hmem,Mem.readW_writeW_self64,onesSum_pair]
  · rw [hflagb]
    apply bit_congr
    rw [pairedZ_norm hgpos]
    constructor
    · rintro ⟨⟨a,b⟩,c⟩; exact ⟨a,pairedZ_prefix.mp ⟨b,c⟩⟩
    · rintro ⟨a,b⟩; exact ⟨⟨a,(pairedZ_prefix.mpr b).1⟩,(pairedZ_prefix.mpr b).2⟩

theorem optimizedHint_paired_vector_ok {p : Params} {S : Nat} {σ s : State} {t : Nat}
    (hp : Ok3 p) (roots : PairedRoots S s) (h : PositiveIH p S σ t 0 s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.hintPairedVector p) s fun u =>
      PositiveIH p S σ t p.k u ∧ PairedRoots S u := by
  unfold Impl.MlDsa.AArch64.Sign.Optimized.hintPairedVector
  have he : 2*(p.k/2)=p.k := by rcases hp with rfl|rfl|rfl <;> decide
  simpa only [Nat.zero_add,he] using seqR_ok
    (I:=fun j s=>PositiveIH p S σ t (2*j) s ∧ PairedRoots S s) (p.k/2) 0
    (fun j _ hj s hs=>by simpa only [Nat.mul_add,Nat.mul_one] using
      optimizedHint_pair_ok hp (by omega : 2*j+1<p.k) hs.2 hs.1) s ⟨by simpa using h,roots⟩

end VG.Proof.MlDsa.AArch64.Sign
