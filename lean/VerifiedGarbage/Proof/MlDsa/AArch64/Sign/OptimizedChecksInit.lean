import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedZ

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (sc)
open VG.Proof.MlKem.AArch64 (Only wp_movz wp_nil)

/-- Reset only the accumulated acceptance flag, preserving memory and roots. -/
theorem positiveFlagInit (s : State) :
    WP isa (.block [.movz .x .x24 1 0]) s fun u => Only [.x24] s u ∧ u.gpr .x24=1 := by
  refine wp_movz fun u hu hv => wp_nil ⟨hu,hv⟩

theorem positiveChecksInit_ok {p : Params} {S : Nat} {σ s : State} {t : Nat}
    (hp : Ok3 p) (hc : ksChk p=true) (h : PositiveChallenge p S σ t s) :
    WP isa (.block kInit) s (PositiveIZ p S σ t 0) := by
  refine ksChk_spec hc fun _ _ _ c4 c5 c6 c7 _ _ _ _ _ _ c13 _ _ c16 _ _ _ _ _ _ _ _ _ c22 _ => ?_
  have hw : ∀w∈[(sc oONES,8)],inB (sgW p) w.1 w.2=true := by
    rcases hp with rfl | rfl | rfl <;> decide
  have b : PositiveKB p S σ t s := ⟨h.c.masks.l,h.ct,h.challenge,h.sampled⟩
  have L := b.l.st.lay
  rw [WP.block_append_iff]
  refine WP.mono_syms (positiveFlagInit s) fun u ⟨hu,hflag⟩ hsu => ?_
  have hpu : PPostB S s u [] := postB24 hu []
  have bu := b.step hpu hsu c13 (by simp)
  refine WP.mono_syms (setQ_ok bu.l.st.lay (by decide) (by decide) c4 (by decide))
    fun v ⟨hpv,hkeep,hm⟩ huv => ?_
  have yv := (h.c.masks.y.keep L hpu c16).keep bu.l.st.lay hpv c6
  exact ⟨⟨bu.step hpv huv c5 hw,by intro j hj; omega,yv.zero,
    (h.c.w.keep L hpu c22).keep bu.l.st.lay hpv c7,
    by rw [hpv.pa (by decide),hm,Mem.readW_writeW_self64]; rfl⟩,
    by rw [hkeep.get .x24,hflag]; exact (bit_one.mpr fun _ hj => by omega).symm⟩

/-- A successfully sampled challenge enters the complete signed-z phase. -/
theorem positiveChallengeZ_ok {p : Params} {S : Nat} {σ s : State} {t : Nat}
    (hp : Ok3 p) (hc : ksChk p=true) (h : PositiveIB p S σ t s)
    (h1 : (s.gpr .x0).setWidth 32=1) :
    WP isa (.seq (VG.Impl.MlDsa.AArch64.Call.callAt "vg_mldsa_ntt_positive"
      VG.Impl.MlDsa.AArch64.Optimized.Ntt.staticNtt
      (VG.Proof.MlDsa.AArch64.Optimized.positiveNttArgs cP))
      (.seq (.block kInit) (VG.Impl.MlDsa.AArch64.Call.seqR
        (Impl.MlDsa.AArch64.Sign.Optimized.zR p) 0 p.ℓ))) s (PositiveIZ p S σ t p.ℓ) := by
  refine WP.seq (WP.mono (positiveChallenge_ok hp h h1) fun u hu => ?_)
  exact WP.seq (WP.mono (positiveChecksInit_ok hp hc hu) fun v hv => optimizedZ_vector_ok hp hv)

end VG.Proof.MlDsa.AArch64.Sign
