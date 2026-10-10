import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedChecks
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedChecksInit
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedR0
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedHintState
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedR0
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedChecksTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedZTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedR0Timing
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsTiming
import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedPairedChecksPrefix
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsExec
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedZTiming

/-! ## From `OptimizedChecksPrefix.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign

/-- A sampled challenge runs every z and r0 check before entering the hint phase. -/
theorem positiveChecksPrefix_ok {p : Params} {S : Nat} {σ s : State} {t : Nat}
    (hp : Ok3 p) (hc : ksChk p=true) (h : PositiveIB p S σ t s)
    (h1 : (s.gpr .x0).setWidth 32=1) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.checksPrefix p) s
      (PositiveIH p S σ t 0) := by
  refine WP.seq (WP.mono (positiveChallengeZ_ok hp hc h h1) fun u hu=>?_)
  exact WP.mono (optimizedR0_vector_ok hp (positiveIR_of_IZ hu)) fun v hv=>positiveIH_of_IR hv

end VG.Proof.MlDsa.AArch64.Sign

end

/-! ## From `OptimizedPairedR0Vector.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign

theorem optimizedR0_paired_vector_ok {p : Params} {S : Nat} {σ s : State} {t : Nat}
    (hp : Ok3 p) (roots : PairedRoots S s) (h : PositiveIR p S σ t 0 s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.pairedLowPhase p) s fun u =>
      PositiveIR p S σ t p.k u ∧ PairedRoots S u := by
  have heven : p.k%2=0 := by rcases hp with rfl|rfl|rfl <;> decide
  unfold Impl.MlDsa.AArch64.Sign.Optimized.pairedLowPhase
  rw [ite_eq_left heven]
  refine WP.seq (WP.mono (seqR_ok (I:=fun j s => PositiveIR p S σ t (2*j) s ∧ PairedRoots S s)
    (p.k/2) 0 (fun j _ hj a ha => ?_) s ⟨by simpa only [Nat.mul_zero] using h,roots⟩) ?_)
  · simpa only [Nat.mul_add,Nat.mul_one] using optimizedR0_pair_ok hp (by omega : 2*j+1<p.k) ha.2 ha.1
  · intro a ha
    have he : 2*(p.k/2)=p.k := by omega
    simp only [Nat.zero_add,he] at ha
    exact WP.block_nil ha

end VG.Proof.MlDsa.AArch64.Sign

end

/-! ## From `OptimizedChecksPrefixTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (callAt)
open VG.Proof.MlDsa.AArch64.Optimized

theorem positiveChallenge_tr {p : Params} {S : Nat} (hp : Ok3 p)
    {t : Nat} {E : State → State → Prop} :
    RelCT isa (RootRS p S E fun σ s=>PositiveIB p S σ t s ∧ (s.gpr .x0).setWidth 32=1)
      (callAt "vg_mldsa_ntt_positive" Impl.MlDsa.AArch64.Optimized.Ntt.staticNtt
        (positiveNttArgs cP)) (RootRS p S E (PositiveChallenge p S · t)) := by
  refine liftRootR (fun _ _ _ h=>positiveChallenge_ok hp h.1 h.2) ?_
  have hc := positiveChallengeChk_ok hp
  simp only [positiveChallengeChk,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨hr,hw⟩,_⟩,_⟩ := hc
  apply positiveNttAt_tr (S := S) (ptr_ok (by decide))
  intro x y h
  obtain ⟨σ,τ,_,_,pub,_,hx,hy⟩ := h.1
  have L := lrel_of pub hx.1.c.masks.l.st hy.1.c.masks.l.st
  have ready (σ s : State) (hs : PositiveIB p S σ t s) (h1 : (s.gpr .x0).setWidth 32=1) :
      NttCallReady cP s := by
    have ls := hs.c.masks.l.st.lay
    have roots := hs.c.masks.l.k.d.roots
    exact ⟨ls.nwp hr,roots.nttTableAt (ls.inW hw),(hs.ok h1).1.1,
      Covers.cons roots.forward.readable (ls.cR hr),ls.cW hw⟩
  exact ⟨ready σ x hx.1 hx.2,ready τ y hy.1 hy.2,L.pa (by decide),L.sp,h.2.1⟩

theorem positiveChecksPrefix_tr {p : Params} {S : Nat} (hp : Ok3 p) (hc : ksChk p=true)
    {t : Nat} {E : State → State → Prop} :
    RelCT isa (RootRS p S E fun σ s=>PositiveIB p S σ t s ∧ (s.gpr .x0).setWidth 32=1)
      (Impl.MlDsa.AArch64.Sign.Optimized.checksPrefix p)
      (RootRS p S E (PositiveIH p S · t 0)) := by
  refine RelCT.seq (RelCT.seq (positiveChallenge_tr hp)
    (RelCT.seq (positiveChecksInit_tr hp hc) (optimizedZ_vector_tr hp))) ?_
  exact RelCT.mono (optimizedR0_vector_tr hp)
    (fun _ _ h=>h.mono (fun _ _ hz=>positiveIR_of_IZ hz))
    (fun _ _ h=>h.mono (fun _ _ hr=>positiveIH_of_IR hr))

end VG.Proof.MlDsa.AArch64.Sign

end

/-! ## From `OptimizedPairedR0Timing.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc seqR)
open VG.Proof.MlDsa.AArch64.Optimized

theorem pairedR0_ready {p : Params} {S : Nat} {σ s : State} {t i : Nat}
    (hp : Ok3 p) (hi : i+1<p.k) (roots : PairedRoots S s) (h : PositiveIR p S σ t i s) :
    Paired.PairedLowReady cP (s2P p i) (wP p i) (hP i) t1P p.γ₂ (p.γ₂-p.β) s := by
  have checks := pairedR0Chk_ok hp i (by omega) hi
  simp only [pairedR0Chk,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at checks
  obtain ⟨⟨⟨⟨⟨⟨cl,hgb⟩,rr⟩,wr⟩,re⟩,we⟩,hws⟩ := checks
  simp only [pairedLowChk,Bool.and_eq_true] at cl
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hc,hs⟩,ho⟩,hl⟩,hw⟩,hwo⟩,hwl⟩,hww⟩,hco⟩,hcl⟩,hcw⟩,hso⟩,hsl⟩,hsw⟩,hol⟩,how⟩,hlw⟩,_⟩ := cl
  obtain ⟨h,_⟩ := h
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
  exact ready

theorem optimizedR0_pair_trace {p : Params} {S : Nat} (hp : Ok3 p) {t r : Nat} (hr : r+1<p.k)
    {E : State → State → Prop} :
    RelCT isa (PairedRS p S E (PositiveIR p S · t r))
      (Impl.MlDsa.AArch64.Sign.Optimized.r0Pair p r) fun _ _=>True := by
  let I := fun tab s => (∃σ,PositiveIR p S σ t r s) ∧ PairedRoots S s ∧ s.syms "VG_MLDSA_INV_PAIR"=tab
  have ht (tab : Addr) : RelCT isa (fun x y => LRel S (sgR p) (sgW p) x y ∧ I tab x ∧ I tab y)
      (Impl.MlDsa.AArch64.Sign.Optimized.r0Pair p r) fun _ _=>True := by
    unfold Impl.MlDsa.AArch64.Sign.Optimized.r0Pair
    refine seqL (I:=I tab) (J:=fun _=>True) ?_ ?_ ?_
    · apply Paired.pairedLowAt_tr (S:=S) (ptr_ok (pS_bases _)) (ptr_ok (pS_bases _))
        (ptr_ok (pS_bases _)) (ptr_ok (pS_bases _)) (ptr_ok (pS_bases _))
      rintro x y ⟨L,⟨⟨σ,hx⟩,rx,ex⟩,⟨⟨τ,hy⟩,ry,ey⟩⟩
      exact ⟨pairedR0_ready hp hr rx hx,pairedR0_ready hp hr ry hy,
        L.pa (by change Reg.x28∈bases; decide),L.pa (by change Reg.x28∈bases; decide),L.pa (by change Reg.x28∈bases; decide),L.pa (by change Reg.x28∈bases; decide),L.pa (by change Reg.x28∈bases; decide),L.sp,ex.trans ey.symm⟩
    · rintro x L ⟨⟨σ,hx⟩,rx,_⟩
      refine WP.mono (Paired.pairedLowAt_ok L.s64 (ptr_ok (pS_bases _)) (ptr_ok (pS_bases _))
        (ptr_ok (pS_bases _)) (ptr_ok (pS_bases _)) (ptr_ok (pS_bases _))
        (pairedR0_ready hp hr rx hx)) fun _ h=>⟨⟨_,h.1.b⟩,trivial⟩
    · exact lrel_tr (fun _ _ h=>h.1) (by taint_decide)
  apply RelCT.mono (RelCT.exists_ ht) ?_ (fun _ _ h=>h)
  intro x y h
  have L := h.1.1.lrel (fun _ _ h=>h.1.1.b.l.st)
  obtain ⟨σ,τ,_,_,_,_,hx,hy⟩ := h.1.1
  exact ⟨x.syms "VG_MLDSA_INV_PAIR",L,⟨⟨σ,hx.1⟩,hx.2,rfl⟩,⟨⟨τ,hy.1⟩,hy.2,h.2.symm⟩⟩

theorem optimizedR0_pair_tr {p : Params} {S : Nat} (hp : Ok3 p) {t r : Nat} (hr : r+1<p.k)
    {E : State → State → Prop} :
    RelCT isa (PairedRS p S E (PositiveIR p S · t r))
      (Impl.MlDsa.AArch64.Sign.Optimized.r0Pair p r) (PairedRS p S E (PositiveIR p S · t (r+2))) :=
  liftPairedR (fun _ _ _ h roots=>optimizedR0_pair_ok hp hr roots h) (optimizedR0_pair_trace hp hr)

theorem optimizedR0_paired_vector_tr {p : Params} {S : Nat} (hp : Ok3 p) {t : Nat}
    {E : State → State → Prop} :
    RelCT isa (PairedRS p S E (PositiveIR p S · t 0))
      (Impl.MlDsa.AArch64.Sign.Optimized.pairedLowPhase p) (PairedRS p S E (PositiveIR p S · t p.k)) := by
  have heven : p.k%2=0 := by rcases hp with rfl|rfl|rfl <;> decide
  unfold Impl.MlDsa.AArch64.Sign.Optimized.pairedLowPhase
  rw [ite_eq_left heven]
  refine RelCT.seq (RelCT.mono (seqR_tr (Q:=fun j=>PairedRS p S E (PositiveIR p S · t (2*j)))
    (p.k/2) 0 (fun j _ hj=>?_)) (fun _ _ h=>by simpa only [Nat.mul_zero] using h)
    (fun _ _ h=>by simpa only [Nat.zero_add] using h)) ?_
  · simpa only [Nat.mul_add,Nat.mul_one] using optimizedR0_pair_tr hp (by omega : 2*j+1<p.k)
  · have he : 2*(p.k/2)=p.k := by omega
    rw [he]
    exact RelCT.block_nil (fun _ _ h=>h)

end VG.Proof.MlDsa.AArch64.Sign

end

/-! ## From `OptimizedPairedChecksPrefix.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (callAt)
open VG.Proof.MlDsa.AArch64.Optimized

theorem positivePairedChallenge_ok {p : Params} {S : Nat} {σ s : State} {t : Nat}
    (hp : Ok3 p) (h16 : 16≤S) (roots : PairedRoots S s)
    (h : PositiveIB p S σ t s) (h1 : (s.gpr .x0).setWidth 32=1) :
    WP isa (callAt "vg_mldsa_ntt_positive" Impl.MlDsa.AArch64.Optimized.Ntt.staticNtt
      (positiveNttArgs cP)) s fun u=>PositiveChallenge p S σ t u ∧ PairedRoots S u := by
  apply WP.pairedRoots (positiveChallenge_ok hp h h1) roots _ h.c.masks.l.st.lay.s64
  exact le_trans (by decide +kernel) h16

theorem positivePairedChecksInit_ok {p : Params} {S : Nat} {σ s : State} {t : Nat}
    (hp : Ok3 p) (hc : ksChk p=true) (roots : PairedRoots S s)
    (h : PositiveChallenge p S σ t s) :
    WP isa (.block kInit) s fun u=>PositiveIZ p S σ t 0 u ∧ PairedRoots S u := by
  apply WP.pairedRoots (positiveChecksInit_ok hp hc h) roots _ h.c.masks.l.st.lay.s64
  change 0≤S
  exact Nat.zero_le _

theorem positivePairedChecksPrefix_ok {p : Params} {S : Nat} {σ s : State} {t : Nat}
    (hp : Ok3 p) (hc : ksChk p=true) (h16 : 16≤S) (roots : PairedRoots S s)
    (h : PositiveIB p S σ t s) (h1 : (s.gpr .x0).setWidth 32=1) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecksPrefix p) s fun u=>
      PositiveIH p S σ t 0 u ∧ PairedRoots S u := by
  unfold Impl.MlDsa.AArch64.Sign.Optimized.pairedChecksPrefix
  refine WP.seq (WP.seq (WP.mono (positivePairedChallenge_ok hp h16 roots h h1) fun a ha=>?_))
  refine WP.seq (WP.mono (positivePairedChecksInit_ok hp hc ha.2 ha.1) fun b hb=>?_)
  refine WP.mono (optimizedZ_paired_vector_ok hp hb.2 hb.1) fun c hc=>?_
  exact WP.mono (optimizedR0_paired_vector_ok hp hc.2 (positiveIR_of_IZ hc.1)) fun d hd=>
    ⟨positiveIH_of_IR hd.1,hd.2⟩

end VG.Proof.MlDsa.AArch64.Sign

end
