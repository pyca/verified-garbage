module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedLoopEnd
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedChecksBase
public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.CachedLoop
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedMaskCopy
public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedPairedChecks

import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedChecksCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedR0
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedChecksBoundary
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedChecksZVector
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsExec
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedLoopInit
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedHints
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Block
import Mathlib.Tactic.FinCases
/-! ## From `CachedLoopFrame.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Sign.CachedChecks
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Sign
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (sc)
variable {f : Poly}

/-- Sampling writes only the challenge and SHAKE work buffers, retaining the
next iteration's cached odd mask even when sampling exhausts its bound. -/
theorem ball_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : Ok3 p) (hc : bChk p=true) {σ s : State} {t : Nat}
    (roots : Roots p S f s) (h : PositiveIC p S σ t s) :
    WP isa (ballAt P (cLen p) p.τ cP) s fun u=>PositiveIB p S σ t u ∧ Roots p S f u := by
  refine both (positiveBall_ok hP hp hc h) ?_
  simp only [bChk,Bool.and_eq_true,decide_eq_true_eq] at hc
  obtain ⟨⟨⟨c1,_⟩,_⟩,hbp⟩ := hc
  refine WP.mono_syms (ballCall_ok hP h.c.masks.l.st.lay hbp c1)
    fun u ⟨hpu,_,_,_,_⟩ hy=>?_
  exact roots.step_layout h.c.masks.l.st.lay hpu hy (challengeWrites_ok hp)
    (by rcases hp with rfl|rfl|rfl <;> decide)

/-- The bounded-sampling failure path changes only the flag and loop counter. -/
theorem ballFailure_ok {S : Nat} {p : Params} (hp : Ok3 p) (hc : lChk p=true)
    {σ s : State} {t : Nat} (roots : Roots p S f s)
    (h : PositiveIB p S σ t s) (h0 : (s.gpr .x0).setWidth 32=0) :
    WP isa (.block (([.movz .x .x24 0 0] : List Instr)++setQ (sc oCNT) 1)) s fun u=>
      PositiveEB p S σ t u ∧ Roots p S f u := by
  refine both (positiveBallFailure_ok hp hc h h0) ?_
  simp only [lChk,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨w1,_⟩,_⟩,_⟩,_⟩,_⟩,_⟩,_⟩,_⟩,_⟩,k0⟩,_⟩,_⟩,_⟩ := hc
  have hz : WP isa (.block [.movz .x .x24 0 0]) s fun u=>
      VG.Proof.MlKem.AArch64.Only [.x24] s u ∧ u.gpr .x24=0 := by
    refine VG.Proof.MlKem.AArch64.wp_movz fun u hu hv=>VG.Proof.MlKem.AArch64.wp_nil ⟨hu,hv⟩
  rw [WP.block_append_iff]
  refine WP.mono_syms hz fun u ⟨hu,_⟩ hy=>?_
  have hpu : PPostB S s u [] := postB24 hu []
  have ku := h.c.masks.l.k.step hpu hy k0 (by simp)
  have ru := roots.step_layout h.c.masks.l.st.lay hpu hy (by simp) (keep_nil hp)
  refine WP.mono_syms (setQ_ok ku.d.im.st.lay (by decide) (by decide) w1 (by decide))
    fun v ⟨hpv,_,_⟩ hyv=>?_
  exact ru.step_layout ku.d.im.st.lay hpv hyv
    (by rcases hp with rfl|rfl|rfl <;> decide) (by rcases hp with rfl|rfl|rfl <;> decide)

/-- Counter decrement retains the cached polynomial on every loop outcome:
accepted, rejected, or bounded-sampling failure. -/
theorem decEnd_ok {S : Nat} {p : Params} (hp : Ok3 p) (hparam : ParamsOk p)
    (hc : lChk p=true) {σ s : State} {t : Nat} (roots : Roots p S f s)
    (h : PositiveEP p S σ t s ∨ PositiveEF p S σ t s ∨ PositiveEB p S σ t s) :
    WP isa (.block cntDec) s fun u=>PositiveLP p S σ t u ∧ Roots p S f u := by
  refine both (positiveDecEnd hp hparam hc h) ?_
  simp only [lChk,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨w1,r1⟩,_⟩,_⟩,_⟩,_⟩,_⟩,_⟩,_⟩,_⟩,_⟩,_⟩,_⟩,_⟩ := hc
  have hk : PositiveIK p S σ s := by rcases h with h|h|h <;> exact h.k
  have L := hk.d.im.st.lay
  refine WP.mono_syms (cntDec_ok s (L.inW w1) (L.inR r1)) fun u ⟨⟨hm,_⟩,k⟩ hy=>?_
  have hf : Frame [⟨pa s (sc oCNT),8⟩] s.mem u.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hpu : PPostB S s u [(sc oCNT,8)] := postB_of_keep k (by decide) hf
  exact roots.step_layout L hpu hy
    (by rcases hp with rfl|rfl|rfl <;> decide) (by rcases hp with rfl|rfl|rfl <;> decide)

end VG.Proof.MlDsa.AArch64.Sign.CachedChecks

end

/-! ## From `CachedChecksLow.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CachedChecks
variable {f : VG.Spec.MlDsa.Poly}
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc)
open VG.Proof.MlDsa.AArch64.Optimized

theorem optimizedR0_rooted_ok {p : Params} {S : Nat} {σ s : State} {t i : Nat}
    (hp : Ok3 p) (hi : i<p.k) (roots : Roots p S f s) (h : PositiveIR p S σ t i s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.r0R p i) s (fun u=>PositiveIR p S σ t (i+1) u ∧ Roots p S f u) := by
  have hc := optimizedR0Chk_ok hp i hi
  simp only [optimizedR0Chk,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨cl,hgb⟩,rp⟩,wp⟩,rr⟩,wr⟩,re⟩,we⟩,hwp⟩ := hc
  simp only [subLowNormChk,Bool.and_eq_true] at cl
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hwr,hcr⟩,hlr⟩,hww⟩,hwl⟩,hwc⟩,hwo⟩,hco⟩,_⟩ := cl
  obtain ⟨h,hflag⟩ := h
  unfold Impl.MlDsa.AArch64.Sign.Optimized.r0R
  refine WP.seq (WP.mono_syms (responseProduct_ok ⟨h.b.l.st,h.b.l.k.d.roots⟩
    (responseProductChk_r0 hp i hi) h.b.c (h.b.l.k.d.s2 i hi)) fun a ⟨hpa,h24a,hprod⟩ hsa => ?_)
  have ra := roots.step_layout h.b.l.st.lay hpa hsa hwp (keep_product hp)
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
  have rb := ra.step_layout ha.b.l.st.lay hpb hsb
    (by simpa using And.intro hww hwl) (keep_low hp hi)
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
  refine ⟨⟨hbstate.step hpc hsc re we (by simp),?_⟩,
    rb.step_layout hbstate.b.l.st.lay hpc hsc (by simp) (keep_nil hp)⟩
  rw [hflagc,bit_and (h24b.trans (h24a.trans hflag)) hret]
  exact bit_congr ⟨fun ⟨⟨a,b⟩,c⟩=>⟨a,forall_lt_succ.mp ⟨b,c⟩⟩,
    fun ⟨a,b⟩=>⟨⟨a,(forall_lt_succ.mpr b).1⟩,(forall_lt_succ.mpr b).2⟩⟩


theorem optimizedR0_pair_ok {p : Params} {S : Nat} {σ s : State} {t i : Nat}
    (hp : Ok3 p) (hi : i+1<p.k) (roots : Roots p S f s) (h : PositiveIR p S σ t i s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.r0Pair p i) s fun u =>
      PositiveIR p S σ t (i+2) u ∧ Roots p S f u := by
  have checks := pairedR0Chk_ok hp i (by omega_arith) hi
  simp only [pairedR0Chk,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at checks
  obtain ⟨⟨⟨⟨⟨⟨cl,hgb⟩,rr⟩,wr⟩,re⟩,we⟩,hws⟩ := checks
  simp only [pairedLowChk,Bool.and_eq_true] at cl
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hc,hs⟩,ho⟩,hl⟩,hw⟩,hwo⟩,hwl⟩,hww⟩,hco⟩,hcl⟩,hcw⟩,hso⟩,hsl⟩,hsw⟩,hol⟩,how⟩,hlw⟩,_⟩ := cl
  obtain ⟨h,hflag⟩ := h
  have hdata : ∀j<2,PolyIs s.mem (pairPolyPtr (pa s (wP p i)) j) (Wv p σ (p.ℓ*t) (i+j)) := by
    intro j hj
    rw [paired_pS_addr]
    simpa only [Nat.add_assoc] using h.w j (by omega_arith)
  have hsecret : ∀j<2,PosPolyIs s.mem (pairPolyPtr (pa s (s2P p i)) j) (S2v p σ (i+j)) := by
    intro j hj
    rw [paired_pS_addr]
    simpa only [Nat.add_assoc] using h.b.l.k.d.s2 (i+j) (by omega_arith)
  have hprod : pairedProductsReduced s.mem (pa s cP) (pa s (s2P p i)) :=
    ⟨h.b.c.bound,fun j hj => (hsecret j hj).bound⟩
  have hdiff : ∀j<2,pairedDifference s.mem (pa s cP) (pa s (s2P p i)) (pa s (wP p i)) j=
      W'v p σ (p.ℓ*t) (i+j) := by
    intro j hj
    simp only [pairedDifference,pairedProduct,(hdata j hj).2,h.b.c.value,(hsecret j hj).value]
    rfl
  have hsep : ∀r∈[⟨pa s (wP p i),2048⟩,⟨pa s (hP i),2048⟩,⟨pa s t1P,2176⟩],
      (⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩:Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl
    · exact roots.roots.apart_write (h.b.l.st.lay.inW hwo)
    · exact roots.roots.apart_write (h.b.l.st.lay.inW hwl)
    · exact roots.roots.apart_write (h.b.l.st.lay.inW hww)
  have ready := pairedLowReady_layout h.b.l.st.lay hc hs ho hl hw hwo hwl hww
    hco hcl hcw hso hsl hsw hol how hlw roots.roots.held roots.roots.fit hsep roots.roots.readable
    hprod (fun j hj => (hdata j hj).1) hgb.1 hgb.2.1 hgb.2.2 roots.roots.aligned
  unfold Impl.MlDsa.AArch64.Sign.Optimized.r0Pair
  refine WP.seq (WP.mono_syms (pairedLowAt_layout h.b.l.st.lay hc hs ho hl hw ready)
    fun a ⟨hpa,h24,hpost⟩ hsa => ?_)
  have ra := roots.step_layout h.b.l.st.lay hpa hsa hws (keep_lowpair hp hi)
  obtain ⟨fields,ret⟩ := hpost.field (VG.Proof.MlDsa.AArch64.Round.isG_of_mem hgb.1) hdiff
  have hhigh : ∀j<2,NatPl a (wBase p+(i+j)) (WHighv p σ (p.ℓ*t) (i+j)) := by
    intro j hj
    have hv := (fields j hj).1
    rw [paired_pS_addr] at hv
    change NatPolyIs a.mem (pa a (pS (wBase p+(i+j)))) _
    rw [hpa.pa (by simp)]
    simpa only [Nat.add_assoc] using hv
  have hlow : ∀j<2,SignedPl a (5+(i+j)) (R0v p σ (p.ℓ*t) (i+j)) (-(p.γ₂:Int)) p.γ₂ := by
    intro j hj
    have hv := (fields j hj).2
    rw [paired_pS_addr] at hv
    change SignedPolyIs a.mem (pa a (pS (5+(i+j)))) _ _ _
    rw [hpa.pa (by simp)]
    simpa only [Nat.add_assoc,pairedLowPoly,R0v,VG.Proof.MlDsa.Sign.r0F] using hv
  simp only [positiveRfam,Bool.and_eq_true] at rr
  have highold := h.high.keep h.b.l.st.lay hpa rr.1.1.2
  have lowold := h.low.keep h.b.l.st.lay hpa rr.1.2
  have highall : NatFam a (wBase p) (i+2) (WHighv p σ (p.ℓ*t)) := by
    simpa only [Nat.add_zero,Nat.add_assoc] using
      (highold.snoc (by simpa only [Nat.add_zero] using hhigh 0 (by decide))).snoc (hhigh 1 (by decide))
  have lowall : SignedFam a 5 (i+2) (R0v p σ (p.ℓ*t)) (-(p.γ₂:Int)) p.γ₂ := by
    simpa only [Nat.add_zero,Nat.add_assoc] using
      (lowold.snoc (by simpa only [Nat.add_zero] using hlow 0 (by decide))).snoc (hlow 1 (by decide))
  have wshift : Fam s (wBase p+(i+2)) (p.k-(i+2)) (fun j=>Wv p σ (p.ℓ*t) (i+2+j)) := by
    simpa only [show i+1+1=i+2 by omega_arith] using ((h.w.shift (by omega_arith)).shift (by omega_arith))
  have ha : PositiveIRb p S σ t (i+2) a :=
    ⟨h.b.step hpa hsa rr.1.1.1.1 hws,h.z.keep h.b.l.st.lay hpa rr.1.1.1.2,
      highall,lowall,wshift.keep h.b.l.st.lay hpa wr,(h.b.l.st.lay.keepW hpa rr.2).trans h.ones⟩
  refine WP.mono_syms (and24_ok a) fun u ⟨hku,hfu⟩ hsu => ?_
  have hpu : PPostB S a u [] := postB24 hku []
  refine ⟨⟨ha.step hpu hsu re we (by simp),?_⟩,ra.step_layout ha.b.l.st.lay hpu hsu (by simp) (keep_nil hp)⟩
  rw [hfu,bit_and (h24.trans hflag) ret]
  apply bit_congr
  change ((ZOk p σ (p.ℓ*t) ∧ ∀j<i,normRq [R0v p σ (p.ℓ*t) j]<p.γ₂-p.β) ∧
    normRq ((List.range 2).map fun j=>R0v p σ (p.ℓ*t) (i+j))<p.γ₂-p.β) ↔ _
  rw [pairedZ_norm (by omega : 0<p.γ₂-p.β),and_assoc,pairedZ_prefix]

end VG.Proof.MlDsa.AArch64.Sign.CachedChecks

end

/-! ## From `CachedChecksHints.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CachedChecks
variable {f : VG.Spec.MlDsa.Poly}
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (sc seqR)
open VG.Proof.MlDsa.AArch64.Optimized

theorem optimizedHint_pair_ok {p : Params} {S : Nat} {σ s : State} {t i : Nat}
    (hp : Ok3 p) (hi : i+1<p.k) (roots : Roots p S f s) (h : PositiveIH p S σ t i s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.hintPair p i) s fun u =>
      PositiveIH p S σ t (i+2) u ∧ Roots p S f u := by
  have hc := pairedHintChk_ok hp i (by omega_arith) hi
  simp only [pairedHintChk,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨kr,zr⟩,hr⟩,lr⟩,fr⟩,orr⟩,wr⟩,kf⟩,zf⟩,hf⟩,lf⟩,ff⟩,ir⟩,iw⟩,hg,hgpos,hk⟩ := hc
  unfold Impl.MlDsa.AArch64.Sign.Optimized.hintPair
  refine WP.seq (WP.mono_syms (pairedHintRow_ok hp hi roots.roots h) fun a ⟨hpa,h24,hint,hret⟩ hsa => ?_)
  obtain ⟨h,hflag⟩ := h
  have ra := roots.step_layout h.b.l.st.lay hpa hsa wr (keep_hintpair hp hi)
  have ba := h.b.step hpa hsa kr wr
  have za := h.z.keep h.b.l.st.lay hpa zr
  have higha := h.high.keep h.b.l.st.lay hpa hr
  have lowshift : SignedFam s (5+(i+2)) (p.k-(i+2))
      (fun j=>R0v p σ (p.ℓ*t) (i+2+j)) (-(p.γ₂:Int)) p.γ₂ := by
    intro j hj
    show SignedPl s (5+(i+2)+j) (R0v p σ (p.ℓ*t) (i+2+j)) _ _
    rw [show 5+(i+2)+j=5+i+(j+2) by omega_arith,show i+2+j=i+(j+2) by omega_arith]
    exact h.low (j+2) (by omega_arith)
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
    omega_arith
  refine WP.mono_syms (hintFinish_semantic (S:=S) a _ _ _ _ (ba.l.st.lay.inR ir)
    (ba.l.st.lay.inW iw) hbound onesa hret (h24.trans hflag)) fun b ⟨hpb,hmem,hflagb⟩ hsb => ?_
  have rb := ra.step_layout ba.l.st.lay hpb hsb (by simpa using iw) (keep_ones hp)
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
    (hp : Ok3 p) (roots : Roots p S f s) (h : PositiveIH p S σ t 0 s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.hintPairedVector p) s fun u =>
      PositiveIH p S σ t p.k u ∧ Roots p S f u := by
  unfold Impl.MlDsa.AArch64.Sign.Optimized.hintPairedVector
  have he : 2*(p.k/2)=p.k := by rcases hp with rfl|rfl|rfl <;> decide
  simpa only [Nat.zero_add,he] using seqR_ok
    (I:=fun j s=>PositiveIH p S σ t (2*j) s ∧ Roots p S f s) (p.k/2) 0
    (fun j _ hj s hs=>by simpa only [Nat.mul_add,Nat.mul_one] using
      optimizedHint_pair_ok hp (by omega_arith : 2*j+1<p.k) hs.2 hs.1) s ⟨by simpa using h,roots⟩

end VG.Proof.MlDsa.AArch64.Sign.CachedChecks

end

/-! ## From `CachedChecksLowVector.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CachedChecks
variable {f : VG.Spec.MlDsa.Poly}
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign

theorem optimizedR0_paired_vector_ok {p : Params} {S : Nat} {σ s : State} {t : Nat}
    (hp : Ok3 p) (roots : Roots p S f s) (h : PositiveIR p S σ t 0 s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.pairedLowPhase p) s fun u =>
      PositiveIR p S σ t p.k u ∧ Roots p S f u := by
  have heven : p.k%2=0 := by rcases hp with rfl|rfl|rfl <;> decide
  unfold Impl.MlDsa.AArch64.Sign.Optimized.pairedLowPhase
  rw [ite_eq_left heven]
  refine WP.seq (WP.mono (seqR_ok (I:=fun j s => PositiveIR p S σ t (2*j) s ∧ Roots p S f s)
    (p.k/2) 0 (fun j _ hj a ha => ?_) s ⟨by simpa only [Nat.mul_zero] using h,roots⟩) ?_)
  · simpa only [Nat.mul_add,Nat.mul_one] using optimizedR0_pair_ok hp (by omega_arith : 2*j+1<p.k) ha.2 ha.1
  · intro a ha
    have he : 2*(p.k/2)=p.k := by omega_arith
    simp only [Nat.zero_add,he] at ha
    exact WP.block_nil ha

end VG.Proof.MlDsa.AArch64.Sign.CachedChecks

end

/-! ## From `CachedChecksCorrect.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CachedChecks
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign

/-- The cached odd mask is retained through every response and hint check.
The frame comes from each callee's actual writes, including its bounded work
area, rather than the overall signer's writable scratch region. -/
theorem checks_ok {p : Params} {S : Nat} {σ s : State} {t : Nat} {f : Poly}
    (hp : Ok3 p) (hc : ksChk p=true) (roots : PairedRoots S s)
    (h : PositiveIB p S σ t s) (h1 : (s.gpr .x0).setWidth 32=1)
    (cache : PolyIs s.mem (pa s t4P) f) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks p) s fun u=>
      (PositiveEP p S σ t u ∨ PositiveEF p S σ t u) ∧ PairedRoots S u ∧
      PolyIs u.mem (pa u t4P) f := by
  unfold Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks
  refine WP.seq (WP.seq (WP.mono (challenge_ok hp ⟨roots,cache⟩ h h1) fun a ha=>?_))
  refine WP.seq (WP.mono (init_ok hp hc ha.2 ha.1) fun b hb=>?_)
  refine WP.mono (earlyPairedSeq_ok (I:=fun r u=>PositiveIZ p S σ t r u ∧ Roots p S f u) p.ℓ 0
    (fun r _ hr s h=>optimizedZ_rooted_ok hp (by omega) h.2 h.1)
    (fun r _ hr s h=>optimizedZ_pair_ok hp (by omega) h.2 h.1) b hb) fun c ⟨nz,_,hnz,hz,hdz⟩=>?_
  rw [Nat.zero_add] at hnz hdz
  have zflag:=PositiveIZ.done hnz hz.1 hdz
  refine ifOkElse_ok (fun hzpass=>?_) fun hzfail=>?_
  · have he:nz=p.ℓ:=hdz.resolve_right hzpass
    subst he
    refine WP.seq (WP.mono (earlyPairedSeq_ok (I:=fun r u=>PositiveIR p S σ t r u ∧ Roots p S f u) p.k 0
      (fun r _ hr s h=>optimizedR0_rooted_ok hp (by omega) h.2 h.1)
      (fun r _ hr s h=>optimizedR0_pair_ok hp (by omega) h.2 h.1) c ⟨positiveIR_of_IZ hz.1,hz.2⟩)
      fun d ⟨nr,_,hnr,hr,hdr⟩=>?_)
    rw [Nat.zero_add] at hnr hdr
    have rflag:=PositiveIR.done hnr hr.1 hdr
    refine ifOkElse_ok (fun hrpass=>?_) fun hrfail=>?_
    · have he:nr=p.k:=hdr.resolve_right hrpass
      subst he
      refine WP.seq (WP.mono (optimizedHint_paired_vector_ok hp hr.2 (positiveIH_of_IR hr.1)) fun e he=>?_)
      refine WP.seq (WP.mono (ones_ok hp hc he.2 he.1) fun a ha=>?_)
      exact WP.mono (branch_ok hp hc ha.2 ha.1) fun u hu=>⟨hu.1,hu.2.roots,hu.2.cache⟩
    · have flag : d.gpr .x24=0 := by
        rw [rflag]; exact bit_zero.mpr (fun h=>(bit_ne.mpr h) (by rw [←rflag]; exact hrfail))
      have fail : ¬ PassV p σ (p.ℓ*t) := by
        intro hpass
        exact (bit_ne.mpr (show ZOk p σ (p.ℓ*t) ∧ R0Ok p σ (p.ℓ*t) from ⟨hpass.1,hpass.2.1⟩))
          (by rw [←rflag]; exact hrfail)
      exact WP.mono (reject_ok hp hc hr.2 hr.1.1.b.l hr.1.1.b.sampled fail flag)
        fun _ hu=>⟨.inr hu.1,hu.2.roots,hu.2.cache⟩
  · have flag : c.gpr .x24=0 := by
      rw [zflag]; exact bit_zero.mpr (fun h=>(bit_ne.mpr h) (by rw [←zflag]; exact hzfail))
    have fail : ¬ PassV p σ (p.ℓ*t) := by
      intro hpass
      exact (bit_ne.mpr hpass.1) (by rw [←zflag]; exact hzfail)
    exact WP.mono (reject_ok hp hc hz.2 hz.1.1.b.l hz.1.1.b.sampled fail flag)
      fun _ hu=>⟨.inr hu.1,hu.2.roots,hu.2.cache⟩

end VG.Proof.MlDsa.AArch64.Sign.CachedChecks

end

/-! ## From `CachedLoopCorrect.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign

/-- The cached commitment has the ordinary commitment result and prepares
exactly the odd mask of the next attempt. -/
def CommitCorrect (P : Prims) (p : Params) (S : Nat) : Prop :=
  ∀σ s t,PositiveIL p S σ t s → PairedRoots S s → (t=0 ∨ Mask p σ t s) →
    WP isa (Impl.MlDsa.AArch64.Sign.Cached.commit P p) s fun u=>
      PositiveIC p S σ t u ∧ PairedRoots S u ∧ Mask p σ (t+1) u

theorem iter_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : Ok3 p) (hb : bChk p=true) (hcommit : CommitCorrect P p S)
    {σ s : State} {t : Nat} (h : PositiveIL p S σ t s) (roots : PairedRoots S s)
    (cache : t=0 ∨ Mask p σ t s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Cached.iter P p (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks p))
      s fun u=>PositiveLP p S σ t u ∧ PairedRoots S u ∧ Mask p σ (t+1) u := by
  unfold Impl.MlDsa.AArch64.Sign.Cached.iter
  refine WP.seq (WP.mono (hcommit σ s t h roots cache) fun a ⟨ha,ra,ca⟩=>?_)
  refine WP.seq (WP.mono (CachedChecks.ball_ok hP hp hb ⟨ra,ca⟩ ha) fun b ⟨hball,rb⟩=>?_)
  refine WP.seq (WP.ite (M:=isa) _ (eval_w0 b) (fun he=>?_) fun he=>?_)
  · have h1 : (b.gpr .x0).setWidth 32=1 := by
      rcases hball.r01 with e|e
      · rw [e] at he; exact absurd he (by decide)
      · exact e
    refine WP.mono (CachedChecks.checks_ok hp (ksChk_ok hp) rb.roots hball h1 rb.cache)
      fun u ⟨hu,ru,cu⟩=>?_
    exact WP.mono (CachedChecks.decEnd_ok hp (paramsOk hp) (lChk_ok hp) ⟨ru,cu⟩
      (hu.elim .inl (fun h=>.inr (.inl h)))) fun v hv=>⟨hv.1,hv.2.roots,hv.2.cache⟩
  · refine WP.mono (CachedChecks.ballFailure_ok hp (lChk_ok hp) rb hball (by simpa using he))
      fun u ⟨hu,ru⟩=>?_
    exact WP.mono (CachedChecks.decEnd_ok hp (paramsOk hp) (lChk_ok hp) ru (.inr (.inr hu)))
      fun v hv=>⟨hv.1,hv.2.roots,hv.2.cache⟩

/-- The first attempt samples its own mask. Every later attempt receives the
cached mask preserved through all checks and the counter decrement. -/
theorem signLoop_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : Ok3 p) (hb : bChk p=true) (hcommit : CommitCorrect P p S)
    {σ s : State} (h : PositiveIK p S σ s) (roots : PairedRoots S s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Cached.signLoop P p (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks p))
      s fun u=>PositiveXS p S σ u ∧ PairedRoots S u := by
  unfold Impl.MlDsa.AArch64.Sign.Cached.signLoop
  refine WP.seq (WP.mono (WP.pairedRoots (positiveLoopInit_ok (lChk_ok hp) h) roots (Nat.zero_le _) hP.s64)
    fun a ⟨ha,ra⟩=>?_)
  refine WP.loop (M:=isa)
    (fun n s=>∃t,n=814-t ∧ PositiveIL p S σ t s ∧ PairedRoots S s ∧ (t=0 ∨ Mask p σ t s))
    (fun n s ⟨t,hn,hs,rs,cs⟩=>?_) 814 a ⟨0,rfl,ha,ra,.inl rfl⟩
  refine WP.mono (iter_ok hP hp hb hcommit hs rs cs) fun u ⟨hu,ru,cu⟩=>?_
  rcases hu with ⟨hz,hi⟩|⟨hz,hx⟩
  · exact .inr ⟨by rw [eval_x9]; simpa using hz,814-(t+1),by have := hs.t_lt; omega_arith,
      t+1,rfl,hi,ru,.inr cu⟩
  · exact .inl ⟨by rw [eval_x9,hz]; rfl,hx,ru⟩

end VG.Proof.MlDsa.AArch64.Sign.Cached

end
