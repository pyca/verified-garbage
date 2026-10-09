import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedCommitmentHash
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseK

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (sc callAt)
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.AArch64.Optimized

structure PositiveIB (p : Params) (S : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  c : PositiveICw p S σ t p.k s
  ct : bytesAt s.mem (pa s (sc oCT)) (cLen p)=CTv p σ (p.ℓ*t)
  r01 : (s.gpr .x0).setWidth 32=0 ∨ (s.gpr .x0).setWidth 32=1
  ok : (s.gpr .x0).setWidth 32=1 → Pl s 0 (toRq (cV p σ (p.ℓ*t))) ∧
    (sampleInBall p.τ maxBounds.ball (CTv p σ (p.ℓ*t))).isSome
  bad : (s.gpr .x0).setWidth 32=0 → sampleInBall p.τ minBounds.ball (CTv p σ (p.ℓ*t))=none

theorem challengeWrites_ok {p : Params} (hp : Ok3 p) :
    ∀w∈[(cP,1024),(sc oPS,2048)],inB (sgW p) w.1 w.2=true := by
  rcases hp with rfl | rfl | rfl <;> decide

theorem positiveBall_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : Ok3 p) (hc : bChk p=true) {σ s : State} {t : Nat} (h : PositiveIC p S σ t s) :
    WP isa (ballAt P (cLen p) p.τ cP) s (PositiveIB p S σ t) := by
  simp only [bChk,Bool.and_eq_true,decide_eq_true_eq] at hc
  obtain ⟨⟨⟨c1,c2⟩,c3⟩,hbp⟩ := hc
  refine WP.mono_syms (ballCall_ok hP h.c.masks.l.st.lay hbp c1)
    fun u ⟨hPu,_,hred,hout,hmax⟩ hy => ?_
  rw [h.ct] at hout hmax
  refine ⟨h.c.step hPu hy c2 (challengeWrites_ok hp),
    by rw [h.c.masks.l.st.lay.keepBytes hPu c3,h.ct],?_,fun h1 => ?_,fun h0 => ?_⟩
  · rcases hout with ⟨e,_⟩ | ⟨e,_⟩
    exacts [.inr e,.inl e]
  · refine ⟨?_,hmax h1⟩
    show PolyIs _ _ _
    rw [hPu.pa (by decide)]
    exact ⟨hred h1,ball_val hout h1 (hmax h1)⟩
  · rcases hout with ⟨e,_⟩ | ⟨_,hn⟩
    · rw [h0] at e; cases e
    · exact Option.map_eq_none_iff.mp hn

/-- Successful challenge sampling, transformed for the fused response calls. -/
structure PositiveChallenge (p : Params) (S : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  c : PositiveICw p S σ t p.k s
  ct : bytesAt s.mem (pa s (sc oCT)) (cLen p)=CTv p σ (p.ℓ*t)
  challenge : PosPl s 0 (ntt (toRq (cV p σ (p.ℓ*t))))
  sampled : (sampleInBall p.τ maxBounds.ball (CTv p σ (p.ℓ*t))).isSome

def positiveChallengeChk (p : Params) : Bool :=
  inB (sgB p) cP 1024 && inB (sgW p) cP 1024 &&
  icwChk p [(cP,1024)] p.k && keepB (sgR p) (sgW p) [(cP,1024)] (sc oCT) (cLen p)

theorem positiveChallengeChk_ok {p : Params} (hp : Ok3 p) : positiveChallengeChk p=true := by
  rcases hp with rfl | rfl | rfl <;> decide +kernel

theorem positiveChallenge_ok {p : Params} {S : Nat} {σ s : State} {t : Nat}
    (hp : Ok3 p) (h : PositiveIB p S σ t s) (h1 : (s.gpr .x0).setWidth 32=1) :
    WP isa (callAt "vg_mldsa_ntt_positive" VG.Impl.MlDsa.AArch64.Optimized.Ntt.staticNtt
      (positiveNttArgs cP)) s (PositiveChallenge p S σ t) := by
  have hc := positiveChallengeChk_ok hp
  simp only [positiveChallengeChk,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨hr,hw⟩,hk⟩,hct⟩ := hc
  obtain ⟨hf,hsampled⟩ := h.ok h1
  have ht : ForwardRoots s (pa s cP) :=
    ⟨h.c.masks.l.k.d.roots.nttTableAt (h.c.masks.l.st.lay.inW hw),h.c.masks.l.k.d.roots.forward.readable⟩
  refine WP.mono_syms (positiveNttAt_layout h.c.masks.l.st.lay hr hw ht hf.1)
    fun u ⟨hPu,_,hv⟩ hy => ?_
  refine ⟨h.c.step hPu hy hk (by simpa using hw),
    by rw [h.c.masks.l.st.lay.keepBytes hPu hct,h.ct],?_,hsampled⟩
  change PosPolyIs u.mem (pa u cP) _
  rw [hPu.pa (by decide)]
  rw [hf.2] at hv
  exact hv

end VG.Proof.MlDsa.AArch64.Sign
