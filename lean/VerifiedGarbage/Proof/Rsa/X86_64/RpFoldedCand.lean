module
import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedExp
import VerifiedGarbage.Proof.Rsa.X86_64.RpCand
public import VerifiedGarbage.Proof.Rsa.X86_64.RpCst

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.R2
import VerifiedGarbage.Proof.Rsa.X86_64.CvLoad
import VerifiedGarbage.Proof.Rsa.X86_64.Inv
public import VerifiedGarbage.Impl.Rsa.X86_64.Recover
public import VerifiedGarbage.Proof.Rsa.Ranges
public import VerifiedGarbage.Proof.Rsa.X86_64.RpBase
public import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedLoop

/-! # Folded prime recovery for one candidate -/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.RecoveryFolded

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys
open VG.Impl.Rsa.X86_64.Keys.Recover VG.Impl.Rsa.X86_64.Keys.Recover.Folded
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aR2 aXm aY aOne sCnt sMask)
open VG.Spec.Rsa (powMod recoverStep)

def candJs : List Nat := [aX, aAcc, aTmp, aXm, aG, aY, aE, aD, aRoot]
def candHs : List Nat := [sMask, sC1, sC2, sC3, sCand]

theorem cand_hs : ∀ i ∈ candHs, rSlot i = true ∧ i ≠ sMinv ∧ i ≠ sT := by decide

/-- Set up the candidate and execute the folded root search. -/
theorem candidate_ok (M : Mont) {u : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    {N el E sigma r a c : Nat}
    (hc : Cst u B Z w minv N el E sigma) (hsigma : sigma ≤ 2)
    (hE : E = r * 4 ^ a) (hr : r % 2 = 1)
    (hcand : word u.mem B (8 * sCand) = BitVec.ofNat 64 c) (hc100 : c < 100) :
    WP isa (candidate M.mm) u fun u' =>
      Cst u' B Z w minv N el E sigma ∧
      Frm B (rg w candJs scanHeaders) u.mem u'.mem ∧ Keep mmRegs u u' ∧
      word u'.mem B (8 * sC3) = mask (recoverStep N (2 * a + sigma) r (c + 2)).isSome ∧
      (∀ y, recoverStep N (2 * a + sigma) r (c + 2) = some y →
        wv u'.mem B (slot w aY) w = y * 2 ^ (64 * w) % N ∧ y < N) := by
  have hZ16 := hc.hZ16
  have hw1 := hc.ws.w1
  have hw2 := hc.ws.w2
  have hR := hc.coprime
  have hN : 2 ^ 64 ≤ N := hc.n1
  simp only [candidate, seqs]
  refine WP.seq (WP.mono (gBlk_ok hc.ws hcand) fun u₁ ⟨hdx, hcx, h12, m₁, k₁⟩ => ?_)
  have hc₁ := hc.congr (js := []) (hs := []) (by rw [m₁]; exact Frm.refl _ _ _) (by simp) (by simp) k₁ (by decide)
  have hg₁ := hc₁.good
  refine WP.seq (WP.mono (setWord_ok hc₁.ws.scr hc₁.ws.rdi hg₁.1.hdr hg₁.2 h12 (by omega) (by omega)
    (o := aX) (by decide) (ri := .rcx) (by decide) (i := 0) (by omega) hcx) fun u₂ ⟨hx₂, o₂, k₂⟩ => ?_)
  rw [hdx, BitVec.toNat_ofNat, Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt (by omega)] at hx₂
  have hf₂ : Frm B (rg w [aX] []) u₁.mem u₂.mem := Frm.rg_of_out o₂ (Nat.le_refl _) _ _ (by decide)
  have hc₂ := hc₁.congr hf₂ (by decide) (by simp) k₂ (by decide)
  have hg₂ := hc₂.good
  -- `g R mod n`.
  refine WP.seq (WP.mono (M.mm_ok hg₂.1 hg₂.2 hw1 (by omega) (o := aXm) (a := aX) (b := aR2) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc₂.hinv
    (by rw [hc₂.hn]; exact hc₂.hr2lt)) fun u₃ ⟨_, hlt₃, hm₃, ha₃, k₃⟩ => ?_)
  rw [hc₂.hn] at hlt₃ hm₃
  rw [hx₂] at hm₃
  have hXm : wv u₃.mem B (slot w aXm) w % N = (c + 2) * 2 ^ (64 * w) % N := g_mont hR hc₂.hr2 hm₃
  have hf₃ : Frm B (rg w [aAcc, aTmp, aXm] []) u₂.mem u₃.mem := Frm.rg_of_arrays ha₃ _ _ (by decide)
  have hc₃ := hc₂.congr hf₃ (by decide) (by simp) k₃ (by decide)
  refine WP.seq (WP.mono (copyA_ok hc₃.ws (o := aG) (a := aXm) (by decide) (by decide) (by decide))
    fun u₄ ⟨hg₄, o₄, k₄⟩ => ?_)
  have hf₄ : Frm B (rg w [aG] []) u₃.mem u₄.mem := Frm.rg_of_out o₄ (by omega) _ _ (by decide)
  have hc₄ := hc₃.congr hf₄ (by decide) (by simp) k₄ (by decide)
  refine WP.seq (WP.mono (copyA_ok hc₄.ws (o := aY) (a := aO) (by decide) (by decide) (by decide))
    fun u₅ ⟨hy₅, o₅, k₅⟩ => ?_)
  have hf₅ : Frm B (rg w [aY] []) u₄.mem u₅.mem := Frm.rg_of_out o₅ (by omega) _ _ (by decide)
  have hc₅ := hc₄.congr hf₅ (by decide) (by simp) k₅ (by decide)
  rw [hc₄.ho] at hy₅
  have hG₅ : wv u₅.mem B (slot w aG) w = wv u₃.mem B (slot w aXm) w := by
    rw [hf₅.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega), hg₄]
  refine WP.mono (exp_ok M hc₅ (g := c + 2) hsigma hE hr
    (by rw [hG₅]; exact hlt₃) (by rw [hG₅]; exact hXm)) fun u' ⟨hcu, hok, hy, f₆, k₆⟩ => ?_
  have f₁ : Frm B (rg w [] []) u.mem u₁.mem := by rw [m₁]; exact Frm.refl _ _ _
  exact ⟨hcu, (((((f₁.rg_trans hf₂).rg_trans hf₃).rg_trans hf₄).rg_trans hf₅).rg_trans f₆).rg_mono (by decide) (by decide),
    (((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k₆).mono (by decide), hok, hy⟩

/-- Candidate counting and stopping are unchanged by folding. -/
theorem candBody_ok (M : Mont) {u : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    {N el E sigma r a c : Nat}
    (hc : Cst u B Z w minv N el E sigma) (hsigma : sigma ≤ 2)
    (hE : E = r * 4 ^ a) (hr : r % 2 = 1)
    (hcand : word u.mem B (8 * sCand) = BitVec.ofNat 64 c) (hc100 : c < 100) :
    WP isa (Folded.candBody M.mm) u fun u' =>
      u'.zf = some (!(decide (c + 1 < 100) && !(recoverStep N (2 * a + sigma) r (c + 2)).isSome)) ∧
      Frm B (rg w candJs candHs) u.mem u'.mem ∧ Keep mmRegs u u' ∧
      word u'.mem B (8 * sCand) = BitVec.ofNat 64 (c + 1) ∧
      word u'.mem B (8 * sC3) = mask (recoverStep N (2 * a + sigma) r (c + 2)).isSome ∧
      (∀ y, recoverStep N (2 * a + sigma) r (c + 2) = some y →
        wv u'.mem B (slot w aY) w = y * 2 ^ (64 * w) % N ∧ y < N) := by
  have h256 := hc.ws.h256
  unfold Folded.candBody
  refine WP.seq (WP.mono (candidate_ok M hc hsigma hE hr hcand hc100)
    fun v ⟨hcv, f₁, k₁, hok, hy⟩ => ?_)
  have hcandv : word v.mem B (8 * sCand) = BitVec.ofNat 64 c := by
    rw [f₁.rg_word (by decide) (by decide)]; exact hcand
  refine WP.mono (candNext_ok hcv.ws hcandv hok hc100) fun u' ⟨hz, m₂, k₂⟩ => ?_
  have f₂ : Frm B (rg w [] [sCand]) v.mem u'.mem := by
    rw [m₂]; exact Frm.rg_of_hdr (writeW_outside _ _ _ (by simp only [sCand, Impl.Bignum.X86_64.Public.sV, sFn]; omega))
      _ _ (List.mem_singleton_self _)
  refine ⟨hz, (f₁.rg_trans f₂).rg_mono (by decide) (by decide), (k₁.trans k₂).mono (by decide),
    by rw [m₂, word_writeW_self], ?_, ?_⟩
  · rw [f₂.rg_word (by decide) (by decide)]; exact hok
  · intro y hsome
    rw [f₂.rg_wv hc.hZ16 (by decide) (by decide) (by decide) (by omega)]
    exact hy y hsome

end VG.Proof.Rsa.X86_64.RecoveryFolded
