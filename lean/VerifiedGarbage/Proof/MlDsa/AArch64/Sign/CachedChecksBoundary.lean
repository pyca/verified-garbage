import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedChecksBase

namespace VG.Proof.MlDsa.AArch64.Sign.CachedChecks
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (sc callAt)
open VG.Proof.MlDsa.AArch64.Optimized
variable {f : Poly}

theorem both {c : Prog isa} {s : State} {Q R : State → Prop}
    (h : WP isa c s Q) (g : WP isa c s R) : WP isa c s fun u=>Q u ∧ R u := by
  obtain ⟨t,u,e,q⟩ := h
  obtain ⟨t',u',e',r⟩ := g
  obtain ⟨_,rfl⟩ := Exec.det e e'
  exact ⟨t,u,e,q,r⟩

theorem challenge_ok {p : Params} {S : Nat} {σ s : State} {t : Nat}
    (hp : Ok3 p) (roots : Roots p S f s) (h : PositiveIB p S σ t s)
    (h1 : (s.gpr .x0).setWidth 32=1) :
    WP isa (callAt "vg_mldsa_ntt_positive" Impl.MlDsa.AArch64.Optimized.Ntt.staticNtt
      (positiveNttArgs cP)) s fun u=>PositiveChallenge p S σ t u ∧ Roots p S f u := by
  refine both (positiveChallenge_ok hp h h1) ?_
  have hc := positiveChallengeChk_ok hp
  simp only [positiveChallengeChk,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨hr,hw⟩,_⟩,_⟩ := hc
  obtain ⟨hf,_⟩ := h.ok h1
  have ht : ForwardRoots s (pa s cP) :=
    ⟨h.c.masks.l.k.d.roots.nttTableAt (h.c.masks.l.st.lay.inW hw),h.c.masks.l.k.d.roots.forward.readable⟩
  refine WP.mono_syms (positiveNttAt_layout h.c.masks.l.st.lay hr hw ht hf.1)
    fun u ⟨hpu,_,_⟩ hy=>?_
  exact roots.step_layout h.c.masks.l.st.lay hpu hy (by simpa using hw)
    (by rcases hp with rfl|rfl|rfl <;> decide)

theorem init_ok {p : Params} {S : Nat} {σ s : State} {t : Nat}
    (hp : Ok3 p) (hc : ksChk p=true) (roots : Roots p S f s)
    (h : PositiveChallenge p S σ t s) :
    WP isa (.block kInit) s fun u=>PositiveIZ p S σ t 0 u ∧ Roots p S f u := by
  refine both (positiveChecksInit_ok hp hc h) ?_
  refine ksChk_spec hc fun _ _ _ c4 c5 _ _ _ _ _ _ _ _ c13 _ _ _ _ _ _ _ _ _ _ _ _ _ _=>?_
  have b : PositiveKB p S σ t s := ⟨h.c.masks.l,h.ct,h.challenge,h.sampled⟩
  rw [WP.block_append_iff]
  refine WP.mono_syms (positiveFlagInit s) fun u ⟨hu,_⟩ hsu=>?_
  have hpu : PPostB S s u [] := postB24 hu []
  have bu := b.step hpu hsu c13 (by simp)
  have ru := roots.step_layout b.l.st.lay hpu hsu (by simp) (keep_nil hp)
  refine WP.mono_syms (setQ_ok bu.l.st.lay (by decide) (by decide) c4 (by decide))
    fun v ⟨hpv,_,_⟩ huv=>?_
  exact ru.step_layout bu.l.st.lay hpv huv
    (by rcases hp with rfl|rfl|rfl <;> decide) (keep_ones hp)

theorem ones_ok {p : Params} {S : Nat} {σ s : State} {t : Nat}
    (hp : Ok3 p) (hc : ksChk p=true) (roots : Roots p S f s)
    (h : PositiveIH p S σ t p.k s) :
    WP isa (.block (onesOk p)) s fun u=>PositiveKO p S σ t u ∧ Roots p S f u := by
  refine both (positiveOnesOk_ok hc h) ?_
  refine ksChk_spec hc fun _ _ _ _ _ _ _ _ _ _ c8 _ _ _ _ _ _ _ _ _ _ _ hω _ _ _ _ _=>?_
  refine WP.mono_syms (onesOk_run p hω s (h.1.b.l.st.lay.inR c8))
    fun u ⟨⟨_,hm⟩,k⟩ hy=>?_
  have hpu : PPostB S s u [] := postB_of_keep k (by decide) (by rw [hm]; exact Frame.refl _ _)
  exact roots.step_layout h.1.b.l.st.lay hpu hy (by simp) (keep_nil hp)

theorem branch_ok {p : Params} {S : Nat} {σ s : State} {t : Nat}
    (hp : Ok3 p) (hc : ksChk p=true) (roots : Roots p S f s)
    (h : PositiveKO p S σ t s) :
    WP isa (ifOkElse (.block (setQ (sc oCNT) 1)) (.block (kapAdd p))) s fun u=>
      (PositiveEP p S σ t u ∨ PositiveEF p S σ t u) ∧ Roots p S f u := by
  refine both (positiveKBranch_ok hp hc h) ?_
  refine ksChk_spec hc fun _ _ _ _ _ _ _ _ _ _ _ c9 c10 _ _ _ _ _ _ _ _ _ _ hl _ _ _ c23=>?_
  have L := h.b.l.st.lay
  refine ifOkElse_ok (fun _=>?_) fun _=>?_
  · refine WP.mono_syms (setQ_ok L (by decide) (by decide) c9 (by decide)) fun u ⟨hpu,_,_⟩ hy=>?_
    exact roots.step_layout L hpu hy
      (by rcases hp with rfl|rfl|rfl <;> decide) (by rcases hp with rfl|rfl|rfl <;> decide)
  · refine WP.mono_syms (kapAdd_ok p hl s (L.inW c10) (L.inR c23)) fun u ⟨hm,k⟩ hy=>?_
    have hf : Frame [⟨pa s (sc oKAP),8⟩] s.mem u.mem := by
      rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    have hpu : PPostB S s u [(sc oKAP,8)] := postB_of_keep k (by decide) hf
    exact roots.step_layout L hpu hy
      (by rcases hp with rfl|rfl|rfl <;> decide) (by rcases hp with rfl|rfl|rfl <;> decide)

end VG.Proof.MlDsa.AArch64.Sign.CachedChecks
