import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedLowRooted
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedZ
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedR0
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowField

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc)
open VG.Proof.MlDsa.AArch64.Optimized

def pairedLowWrites (p : Params) (i : Nat) : List (Ptr × Nat) :=
  [(wP p i,2048),(hP i,2048),(t1P,2176)]

def pairedR0Chk (p : Params) (i : Nat) : Bool :=
  let ws := pairedLowWrites p i
  pairedLowChk p i && decide (p.γ₂∈gamma2s ∧ 1≤p.γ₂-p.β ∧ p.γ₂-p.β≤524288) &&
  positiveRfam p ws i && famChk (sgR p) (sgW p) ws (wBase p+(i+2)) (p.k-(i+2)) &&
  positiveRfam p [] (i+2) && famChk (sgR p) (sgW p) [] (wBase p+(i+2)) (p.k-(i+2)) &&
  ws.all (fun w=>inB (sgW p) w.1 w.2)

theorem pairedR0Chk_ok {p : Params} (hp : Ok3 p) : ∀i<p.k,i+1<p.k → pairedR0Chk p i=true := by
  rcases hp with rfl|rfl|rfl <;> decide

theorem optimizedR0_pair_ok {p : Params} {S : Nat} {σ s : State} {t i : Nat}
    (hp : Ok3 p) (hi : i+1<p.k) (roots : PairedRoots S s) (h : PositiveIR p S σ t i s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.r0Pair p i) s fun u =>
      PositiveIR p S σ t (i+2) u ∧ PairedRoots S u := by
  have checks := pairedR0Chk_ok hp i (by omega) hi
  simp only [pairedR0Chk,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at checks
  obtain ⟨⟨⟨⟨⟨⟨cl,hgb⟩,rr⟩,wr⟩,re⟩,we⟩,hws⟩ := checks
  simp only [pairedLowChk,Bool.and_eq_true] at cl
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hc,hs⟩,ho⟩,hl⟩,hw⟩,hwo⟩,hwl⟩,hww⟩,hco⟩,hcl⟩,hcw⟩,hso⟩,hsl⟩,hsw⟩,hol⟩,how⟩,hlw⟩,_⟩ := cl
  obtain ⟨h,hflag⟩ := h
  have hdata : ∀j<2,PolyIs s.mem (pairPolyPtr (pa s (wP p i)) j) (Wv p σ (p.ℓ*t) (i+j)) := by
    intro j hj
    rw [paired_pS_addr]
    simpa only [Nat.add_assoc] using h.w j (by omega)
  have hsecret : ∀j<2,PosPolyIs s.mem (pairPolyPtr (pa s (s2P p i)) j) (S2v p σ (i+j)) := by
    intro j hj
    rw [paired_pS_addr]
    simpa only [Nat.add_assoc] using h.b.l.k.d.s2 (i+j) (by omega)
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
    · exact roots.apart_write (h.b.l.st.lay.inW hwo)
    · exact roots.apart_write (h.b.l.st.lay.inW hwl)
    · exact roots.apart_write (h.b.l.st.lay.inW hww)
  have ready := pairedLowReady_layout h.b.l.st.lay hc hs ho hl hw hwo hwl hww
    hco hcl hcw hso hsl hsw hol how hlw roots.held roots.fit hsep roots.readable
    hprod (fun j hj => (hdata j hj).1) hgb.1 hgb.2.1 hgb.2.2
  unfold Impl.MlDsa.AArch64.Sign.Optimized.r0Pair
  refine WP.seq (WP.mono_syms (pairedLowAt_layout h.b.l.st.lay hc hs ho hl hw ready)
    fun a ⟨hpa,h24,hpost⟩ hsa => ?_)
  have ra := roots.step_layout h.b.l.st.lay hpa hsa hws
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
    simpa only [show i+1+1=i+2 by omega] using ((h.w.shift (by omega)).shift (by omega))
  have ha : PositiveIRb p S σ t (i+2) a :=
    ⟨h.b.step hpa hsa rr.1.1.1.1 hws,h.z.keep h.b.l.st.lay hpa rr.1.1.1.2,
      highall,lowall,wshift.keep h.b.l.st.lay hpa wr,(h.b.l.st.lay.keepW hpa rr.2).trans h.ones⟩
  refine WP.mono_syms (and24_ok a) fun u ⟨hku,hfu⟩ hsu => ?_
  have hpu : PPostB S a u [] := postB24 hku []
  refine ⟨⟨ha.step hpu hsu re we (by simp),?_⟩,ra.step_layout ha.b.l.st.lay hpu hsu (by simp)⟩
  rw [hfu,bit_and (h24.trans hflag) ret]
  apply bit_congr
  change ((ZOk p σ (p.ℓ*t) ∧ ∀j<i,normRq [R0v p σ (p.ℓ*t) j]<p.γ₂-p.β) ∧
    normRq ((List.range 2).map fun j=>R0v p σ (p.ℓ*t) (i+j))<p.γ₂-p.β) ↔ _
  rw [pairedZ_norm (by omega : 0<p.γ₂-p.β),and_assoc,pairedZ_prefix]

end VG.Proof.MlDsa.AArch64.Sign
