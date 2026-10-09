import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedMasks
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseL

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc)

theorem PositiveIK.step {p : Params} {S : Nat} {σ s u : State} (h : PositiveIK p S σ s)
    {ws : List (Ptr × Nat)} (hP : PPostB S s u ws) (hy : u.syms=s.syms)
    (hc : ikChk p ws=true) (hw : ∀w∈ws,inB (sgW p) w.1 w.2=true) : PositiveIK p S σ u := by
  simp only [ikChk,Bool.and_eq_true] at hc
  exact ⟨h.d.step hP hy hc.1 hw,(h.d.im.st.lay.keepBytes hP hc.2).trans h.rpp⟩

/-- The original counter stores establish the optimized loop invariant:
nonce zero, 814 attempts remaining, and no earlier rejected attempts. -/
theorem positiveLoopInit_ok {S : Nat} {p : Params} (hc : lChk p=true) {σ s : State}
    (h : PositiveIK p S σ s) :
    WP isa (.block (setQ (sc oKAP) 0 ++ setQ (sc oCNT) 814)) s (PositiveIL p S σ 0) := by
  simp only [lChk,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨w1,_⟩,k1⟩,kk⟩,_⟩,_⟩,_⟩,_⟩,_⟩,_⟩,_⟩,_⟩,wk⟩,ik⟩ := hc
  rw [WP.block_append_iff]
  refine WP.mono_syms (setQ_ok h.d.im.st.lay (by decide) (by decide) wk (by decide))
    fun s1 ⟨hP1,_,hm1⟩ hy1 => ?_
  have K1 := h.step hP1 hy1 ik (by simpa using wk)
  refine WP.mono_syms (setQ_ok K1.d.im.st.lay (by decide) (by decide) w1 (by decide))
    fun s2 ⟨hP2,_,hm2⟩ hy2 => ?_
  exact ⟨K1.step hP2 hy2 k1 (by simpa using w1),by
      rw [K1.d.im.st.lay.keepW hP2 kk,hP1.pa (by decide),hm1,Mem.readW_writeW_self64]; rfl,
    by rw [hP2.pa (by decide),hm2,Mem.readW_writeW_self64],by decide,
    fun _ h => absurd h (Nat.not_lt_zero _)⟩

end VG.Proof.MlDsa.AArch64.Sign
