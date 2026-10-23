module
public import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedCTMont
public import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedCands
import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedCTExp
public import VerifiedGarbage.Proof.Rsa.X86_64.RpCT6

import VerifiedGarbage.Proof.Rsa.RecoverTries
import VerifiedGarbage.Proof.Rsa.X86_64.RpCT4
import VerifiedGarbage.Proof.Rsa.X86_64.CvLoad
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpCT3
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpCands
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpWindowCTPrepare
meta import VerifiedGarbage.Proof.Rsa.RecoverTries
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpCT4
meta import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
meta import VerifiedGarbage.Proof.Rsa.X86_64.CvLoad
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Rsa.X86_64.RecoverFolded
public import VerifiedGarbage.Proof.Rsa.RecoverFolded
public import VerifiedGarbage.Proof.Rsa.RecoverMath
public import VerifiedGarbage.Proof.Rsa.X86_64.RpCT1
public import VerifiedGarbage.Proof.Rsa.X86_64.RpCst

/-! # Constant time of folded candidate recovery -/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.RecoveryFolded

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aR2 aXm aY aOne sCnt sMask)
open VG.Spec.Rsa (splitTwos recoverStep recoverPrimes recoverTries)

open VG.Impl.Rsa.X86_64.Keys.Recover.Folded
open Rp

theorem candidate_ct (M : Mont) : RelCT isa (Two CA)
    (candidate M.mm)
    fun _ _ => True := by
  have hK : ∀ p s, CK p s → Ws s p.B p.Z (wk p.k) := fun _ _ h => h.ws
  have hX : ∀ j p s, CX j p s → Ws s p.B p.Z (wk p.k) := fun _ _ _ ⟨_, _, _, _, _, hc, _⟩ => hc.ws
  simp only [candidate, seqs]
  refine RelCT.seq (R := Two CG) (blk_gct RpP.B RpP.Z (fun p => wk p.k)
    (fun _ _ ⟨_, _, _, _, _, hc, _⟩ => hc.ws) (by taint_decide) fun p s h => ?_) ?_
  · obtain ⟨minv, N, r, t, c, hc, hcand, -⟩ := h
    exact WP.mono (gBlk_ok hc.ws hcand) fun u ⟨_, hcx, h12, m, k⟩ =>
      ⟨minv, N, r, t, hc.congr (js := []) (hs := []) (by rw [m]; exact Frm.refl _ _ _) (by simp) (by simp) k
        (by decide), h12, hcx⟩
  refine RelCT.seq setX_ct (RelCT.seq (R := Two (CX aXm)) (mm_gct RpP.B RpP.Z (fun p => wk p.k) hK M
    (o := aXm) (a := aX) (b := aR2) (by unfold MmUse; decide) fun p s h => ?_) ?_)
  · obtain ⟨minv, N, r, t, hc⟩ := h
    have hg := hc.good
    have hw2 := hc.ws.w2
    refine WP.mono (M.mm_ok hg.1 hg.2 hc.ws.w1 (by omega) (o := aXm) (a := aX) (b := aR2) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.hinv
      (by rw [hc.hn]; exact hc.hr2lt)) fun u ⟨_, hlt, hm, ha, k⟩ => ?_
    rw [hc.hn] at hlt hm
    exact ⟨minv, N, r, t, _, hc.congr (Frm.rg_of_arrays ha [aXm, aAcc, aTmp] [] (by decide)) (by decide) (by simp)
      k (by decide), hlt, g_mont hc.coprime hc.hr2 hm⟩
  refine RelCT.seq (R := Two (CX aG)) (copyA_gct RpP.B RpP.Z (fun p => wk p.k) (hX aXm) (by taint_decide)
    fun p s h => ?_) (RelCT.seq (R := Two Rp.EX) (copyA_gct RpP.B RpP.Z (fun p => wk p.k) (hX aG) (by taint_decide)
      fun p s h => ?_) ((exp_ct M).mono (fun _ _ h => h) fun _ _ _ => trivial))
  · obtain ⟨minv, N, r, t, g, hc, hlt, hm⟩ := h
    have hZ16 := hc.hZ16
    refine WP.mono (copyA_ok hc.ws (o := aG) (a := aXm) (by decide) (by decide) (by decide)) fun u ⟨hv, o, k⟩ => ?_
    have hf : Frm p.B (rg (wk p.k) [aG] []) s.mem u.mem := Frm.rg_of_out o (by omega) _ _ (by decide)
    exact ⟨minv, N, r, t, g, hc.congr hf (by decide) (by simp) k (by decide), by rw [hv]; exact hlt,
      by rw [hv]; exact hm⟩
  · obtain ⟨minv, N, r, t, g, hc, hlt, hm⟩ := h
    have hZ16 := hc.hZ16
    refine WP.mono (copyA_ok hc.ws (o := aY) (a := aO) (by decide) (by decide) (by decide)) fun u ⟨hv, o, k⟩ => ?_
    have hf : Frm p.B (rg (wk p.k) [aY] []) s.mem u.mem := Frm.rg_of_out o (by omega) _ _ (by decide)
    have hG : wv u.mem p.B (slot (wk p.k) aG) (wk p.k) = wv s.mem p.B (slot (wk p.k) aG) (wk p.k) :=
      hf.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega)
    exact ⟨minv, N, r, t, g, hc.congr hf (by decide) (by simp) k (by decide), by rw [hG]; exact hlt,
      by rw [hG]; exact hm, by rw [hv, hc.ho]⟩

def FCA (p : RpP) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (N E sigma r a c : Nat), Cst s p.B p.Z (wk p.k) minv N p.el E sigma ∧
    sigma ≤ 2 ∧ E = r * 4 ^ a ∧ r % 2 = 1 ∧ word s.mem p.B (8 * sCand) = BitVec.ofNat 64 c ∧ c < 100

theorem candBody_ct (M : Mont) : RelCT isa (Two FCA) (Folded.candBody M.mm) fun _ _ => True := by
  unfold Folded.candBody
  refine RelCT.seq (R := Two CK) (two_post (two_map (Φ' := CA) id (fun p s h => ?_) (candidate_ct M)) ?_) ?_
  · obtain ⟨minv, N, E, sigma, r, a, c, hc, _, _, _, hCand, hc100⟩ := h
    exact ⟨minv, N, E, sigma, c, hc, hCand, hc100⟩
  · intro p s ⟨minv, N, E, sigma, r, a, c, hc, hsigma, hE, hr, hCand, hc100⟩
    exact WP.mono (candidate_ok M hc hsigma hE hr hCand hc100) fun _ ⟨hc', _⟩ =>
      ⟨minv, N, E, sigma, hc'⟩
  · exact two_taint [.rdi] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.ws.rdi, h₂.ws.rdi]) (by taint_decide)

def CL (p : RpP) (j : Nat) (u : State) : Prop :=
  ∃ (s₀ : State) (minv : BitVec 64) (N E sigma r a : Nat),
    Cst s₀ p.B p.Z (wk p.k) minv N p.el E sigma ∧ sigma ≤ 2 ∧ E = r * 4 ^ a ∧ r % 2 = 1 ∧
    p.cnt = (recoverPrimes.go N (2 * a + sigma) r recoverTries).2 ∧
    CandI s₀ p.B (wk p.k) N (2 * a + sigma) r j u

theorem candLoopL_ct (M : Mont) : RelCT isa (Two fun p s => 0 < p.cnt ∧ CL p 0 s) (.loop (Folded.candBody M.mm) .ne)
    (Two fun (_ : RpP) (_ : State) => True) :=
  two_loop RpP.cnt (two_map (fun q => q.1) (fun q s hq => by
      obtain ⟨hj, s₀, minv, N, E, sigma, r, a, hc, hsigma, hE, hr, hcnt, hI⟩ := hq
      have := go_le N (2 * a + sigma) r recoverTries (Nat.le_refl _)
      exact ⟨minv, N, E, sigma, r, a, q.2, hc.congr hI.frm (by decide) cand_hs hI.keep (by decide), hsigma, hE, hr, hI.cand,
        by have : recoverTries = 100 := rfl; omega⟩) (candBody_ct M))
    fun p j s hj ⟨s₀, minv, N, E, sigma, r, a, hc, hsigma, hE, hr, hcnt, hI⟩ => by
      have hle := go_le N (2 * a + sigma) r recoverTries (Nat.le_refl _)
      have hj100 : j < 100 := by have : recoverTries = 100 := rfl; omega
      have hcu := hc.congr hI.frm (by decide) cand_hs hI.keep (by decide)
      refine WP.mono (candBody_ok M hcu hsigma hE hr hI.cand hj100) fun u' ⟨hz, hf, k, hcand, _, _⟩ => ⟨?_, fun hlt => ?_,
        fun _ => trivial⟩
      · rw [hcnt] at hj ⊢
        simp only [eval, hz, Option.map_some]
        exact congrArg some (cand_cond N (2 * a + sigma) r hj hI.go)
      · refine ⟨s₀, minv, N, E, sigma, r, a, hc, hsigma, hE, hr, hcnt, (hI.frm.rg_trans hf).rg_mono (by decide) (by decide),
          (hI.keep.trans k).mono (by decide), hcand, ?_⟩
        rw [hI.go, VG.Proof.Rsa.go_eq N (2 * a + sigma) r hj100]
        rw [hcnt, hI.go, VG.Proof.Rsa.go_eq N (2 * a + sigma) r hj100] at hlt
        cases hs : recoverStep N (2 * a + sigma) r (j + 2) with
        | some y => rw [hs] at hlt; exact absurd hlt (by simp)
        | none => rfl

def GR3 (p : RpP) (s : State) : Prop :=
  ∃ (I : RpIn) (m₀ : Mem) (minv : BitVec 64) (res : Option Nat) (cnt : Nat), I.pub = p ∧ RpS I m₀ s ∧
    RpLens I ∧ RpOuts I ∧ Spec.Rsa.modulusValid I.N I.k = true ∧
    Cst s I.B I.Z (wk I.k) minv I.N I.el ((I.D * I.E - 1) / 2 ^ VG.Proof.Rsa.RecoveryFolded.sigma (splitTwos (I.D * I.E - 1)).1)
      (VG.Proof.Rsa.RecoveryFolded.sigma (splitTwos (I.D * I.E - 1)).1) ∧
    recoverPrimes.go I.N (splitTwos (I.D * I.E - 1)).1 (splitTwos (I.D * I.E - 1)).2 recoverTries =
      (res.map (pqOf I.N), cnt) ∧ word s.mem I.B (8 * sC3) = mask res.isSome ∧
    (∀ y, res = some y → wv s.mem I.B (slot (wk I.k) aY) (wk I.k) = y * 2 ^ (64 * wk I.k) % I.N ∧ y < I.N ∧
      y * y % I.N = 1)

theorem split_even {m : Nat} (hm : 0 < m) (he : m % 2 = 0) : 1 ≤ (splitTwos m).1 := by
  have hs := VG.Proof.Rsa.splitTwos_spec hm
  by_contra h
  have hz : (splitTwos m).1 = 0 := by omega
  rw [hz, Nat.pow_zero, Nat.one_mul] at hs
  omega

theorem candLoop_ct (M : Mont) : RelCT isa (Two GR2) (Folded.candLoop M.mm) (Two GR3) := by
  refine two_post ?_ ?_
  · unfold Folded.candLoop
    refine RelCT.seq (blk_gct RpP.B RpP.Z (fun p => wk p.k)
      (fun _ _ ⟨_, _, e, S, _⟩ => e ▸ S.ws) (by taint_decide) ?_)
      ((candLoopL_ct M).mono (fun _ _ h => h) (fun _ _ _ => trivial))
    intro p s h
    obtain ⟨I, m₀, rfl, S, L, O, hv, hc, hm0, heven⟩ := h
    have ht1 := split_even hm0 heven
    have hspl := VG.Proof.Rsa.splitTwos_spec hm0
    have hsigma := VG.Proof.Rsa.RecoveryFolded.sigma_bounds (splitTwos (I.D * I.E - 1)).1
    have hE := VG.Proof.Rsa.RecoveryFolded.aligned_exponent hm0 ht1
    have hcnt := cnt_eq hv L hm0 heven
    rw [VG.Proof.Rsa.RecoveryFolded.aligned_twos ht1] at hcnt
    dsimp only [RpIn.pub]
    have h256 := hc.ws.h256
    refine WP.mono (WP.keep [.rax] (Q := fun u => u.mem = s.mem.writeW (off I.B (8 * sCand))
      (BitVec.ofNat 64 0)) (by
      xrun [State.ea, hdr, hc.ws.rdi, hdrOff,
        hc.ws.scr.st (d := 8 * sCand) (by simp only [sCand, Impl.Bignum.X86_64.Public.sV, sFn]; omega)]
      rfl) rfl) fun u ⟨mu, ku⟩ => ⟨?_, s, _, I.N, _, _, _, _, hc, hsigma.2, hE, hspl.2, hcnt,
        ?_, ku.mono (by decide), by rw [mu, word_writeW_self], rfl⟩
    · rw [show (Spec.Rsa.primesKey I.nb I.eb I.db).2 = I.pub.cnt from rfl, hcnt]
      exact VG.Proof.Rsa.go_pos _ _ _ _ (Nat.le_refl _)
    · rw [mu]; exact Frm.rg_of_hdr (writeW_outside _ _ _ (by simp only [sCand, Impl.Bignum.X86_64.Public.sV, sFn]; omega))
        _ _ (by decide)
  · intro p s h
    obtain ⟨I, m₀, rfl, S, L, O, hv, hc, hm0, heven⟩ := h
    have ht1 := split_even hm0 heven
    have hspl := VG.Proof.Rsa.splitTwos_spec hm0
    have hsigma := VG.Proof.Rsa.RecoveryFolded.sigma_bounds (splitTwos (I.D * I.E - 1)).1
    refine WP.mono (candLoop_ok M hc hsigma.2 (VG.Proof.Rsa.RecoveryFolded.aligned_exponent hm0 ht1) hspl.2)
      fun u ⟨res, cnt, hgo, _, hc3, hy, f, k⟩ => ?_
    rw [← VG.Proof.Rsa.RecoveryFolded.aligned_twos ht1] at hgo
    exact ⟨I, m₀, _, res, cnt, rfl, S.step f (by decide) (by decide) k (by decide), L, O, hv,
      hc.congr f (by decide) cand_hs k (by decide), hgo, hc3, hy⟩

end VG.Proof.Rsa.X86_64.RecoveryFolded
