import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedLowCheck
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRoots

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Impl.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.AArch64.Optimized

theorem pairedLow_rooted {p : Params} {S : Nat} {σ s : State} {i : Nat}
    (hchk : pairedLowChk p i=true) (hstate : RootedSt p S σ s) (hroots : PairedRoots S s)
    (hprod : pairedProductsReduced s.mem (pa s cP) (pa s (s2P p i)))
    (hcan : ∀j<2,Reduced s.mem (pairPolyPtr (pa s (wP p i)) j))
    (hg : p.γ₂∈gamma2s) (hB : 1≤p.γ₂-p.β) (hB' : p.γ₂-p.β≤524288) :
    WP isa (callAt "vg_mldsa_fused_pair_r0" (VG.Impl.MlDsa.AArch64.Optimized.Paired.selected .r0)
      (Paired.pairedLowArgs cP (s2P p i) (wP p i) (hP i) t1P p.γ₂ (p.γ₂-p.β))) s fun t =>
      RootedSt p S σ t ∧ PairedRoots S t ∧ t.gpr .x24=s.gpr .x24 ∧
      Paired.PairedLowPost p.γ₂ (p.γ₂-p.β) s.mem t.mem (pa t cP) (pa t (s2P p i))
        (pa t (wP p i)) (pa t (hP i)) ((t.gpr .x0).setWidth 32) := by
  simp only [pairedLowChk,Bool.and_eq_true] at hchk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hc,hs⟩,ho⟩,hl⟩,hw⟩,hwo⟩,hwl⟩,hww⟩,hco⟩,hcl⟩,hcw⟩,hso⟩,hsl⟩,hsw⟩,hol⟩,how⟩,hlw⟩,hst⟩ := hchk
  have hsep : ∀r∈[⟨pa s (wP p i),2048⟩,⟨pa s (hP i),2048⟩,⟨pa s t1P,2176⟩],
      (⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩:Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl
    · exact hroots.apart_write (hstate.1.lay.inW hwo)
    · exact hroots.apart_write (hstate.1.lay.inW hwl)
    · exact hroots.apart_write (hstate.1.lay.inW hww)
  have hready := pairedLowReady_layout hstate.1.lay hc hs ho hl hw hwo hwl hww
    hco hcl hcw hso hsl hsw hol how hlw hroots.held hroots.fit hsep hroots.readable hprod hcan hg hB hB'
  refine WP.mono_syms (pairedLowAt_layout hstate.1.lay hc hs ho hl hw hready) fun t ⟨hp,h24,hv⟩ hy => ?_
  have hwrites : ∀w∈[(wP p i,2048),(hP i,2048),(t1P,2176)],inB (sgW p) w.1 w.2=true := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq] using And.intro hwo (And.intro hwl hww)
  refine ⟨hstate.step hp hy hst hwrites,hroots.step hp hy ?_,h24,?_⟩
  · intro w hm
    exact hstate.1.lay.inW (hwrites w hm)
  · rw [hp.pa (hstate.1.lay.ptrBs hc),hp.pa (hstate.1.lay.ptrBs hs),
      hp.pa (hstate.1.lay.ptrBs ho),hp.pa (hstate.1.lay.ptrBs hl)]
    exact hv

end VG.Proof.MlDsa.AArch64.Sign
