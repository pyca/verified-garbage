module
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PrimeSetup
public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.MontPrep

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Close
import VerifiedGarbage.Proof.Rsa.Ranges
import VerifiedGarbage.Proof.Bignum.Math

/-! Complete the Montgomery constants using the shared arithmetic backend. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.RsaKeyGen.AArch64 VG.Proof.Ffdh.AArch64.ParameterCandidate
open VG.Proof.MlKem.AArch64 (Keep)

theorem primeConstants_ok (M : Mont) {s : State} {B : Addr} {Z w N : Nat}
    (h : Ws s B Z w) (hn : wv s.mem B (slot w aN) w = N)
    (hodd : N % 2 = 1) (hN1 : 1 < N)
    (hinv : ((word s.mem B (slot w aN)).toNat * (word s.mem B (8 * sMinv)).toNat + 1) % 2 ^ 64 = 0)
    (hone : wv s.mem B (slot w aOne) w = 1)
    (hr2 : wv s.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % N) :
    WP isa (seqs (Impl.Dsa.AArch64.Generation.primeConstants M.mm)) s fun t =>
      Ws t B Z w ∧ wv t.mem B (slot w aR1) w = 2 ^ (64 * w) % N ∧
      wv t.mem B (slot w aRm1) w = N - 2 ^ (64 * w) % N ∧
      wv t.mem B (slot w aOne) w = 1 ∧
      wv t.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % N ∧
      Frm B (mpTail w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hnw := h.scr.nowrap
  have hZ := h.hZ
  have hZ16 : 256 + 16 * (8 * (w + 2)) ≤ Z := by simpa only [slot, hdrBytes] using hZ
  have hZ8 := h.good.2
  have hw' : w < 2 ^ 31 := by have := h.w2; omega
  have hR : Nat.Coprime (2 ^ (64 * w)) N := VG.Proof.Bignum.coprime_pow2 hodd _
  have hNlt : N < 2 ^ (64 * w) := hn ▸ wv_lt _ _ _ _
  unfold Impl.Dsa.AArch64.Generation.primeConstants
  refine wp_seqs_append (by simp) (by simp [subA]) ?_
  simp only [seqs]
  refine WP.seq (WP.mono (M.mm_ok h.good.1 hZ8 h.w1 hw' (o := aY) (a := aR2) (b := aOne)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hinv
    (by rw [hone, hn]; exact hN1)) fun u ⟨_, hlt, hy, ha, ku⟩ => ?_)
  rw [hn, hr2, hone] at hy
  rw [hn] at hlt
  have hY : wv u.mem B (slot w aY) w = 2 ^ (64 * w) % N := by
    rw [← Nat.mod_eq_of_lt hlt]
    refine VG.Proof.Bignum.mont_cancel hR ?_
    rw [hy, Nat.mul_one, Nat.mod_mod]
  have fu : Frm B (mpTail w) s.mem u.mem := Frm.of_arrays ha (by simp [mpTail])
  have hu : Ws u B Z w := h.congr' fu (mpTail_kmut w) ku (by decide)
  refine WP.mono (copyA_ok hu (o := aR1) (a := aY) (by decide) (by decide) (by decide))
    fun v ⟨hv, ov, _, _, kv⟩ => ?_
  rw [hY] at hv
  have fv : Frm B (mpTail w) u.mem v.mem :=
    Frm.of_outside (ov.mono (o' := slot w aR1) (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega))
      (by simp [mpTail])
  have Fv := fu.trans fv
  have huv : Ws v B Z w := h.congr' Fv (mpTail_kmut w) (ku.trans kv) (by decide)
  have hnv := (mp_fix Fv hnw hZ).2.2.trans hn
  refine WP.mono (subA_ok huv (o := aRm1) (a := aN) (b := aR1)
    (by decide) (by decide) (by decide) (.inr (by decide)) (by decide))
    fun t ⟨ht, ot, _, _, _, kt⟩ => ?_
  rw [hv, hnv] at ht
  have hRm : wv t.mem B (slot w aRm1) w = N - 2 ^ (64 * w) % N := by
    have hx := wv_lt t.mem B (slot w aRm1) w
    have hm := Nat.mod_lt (2 ^ (64 * w)) (show 0 < N by omega)
    cases hc : (!t.c) <;> rw [hc] at ht <;>
      simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at ht <;> omega
  have ft : Frm B (mpTail w) v.mem t.mem :=
    Frm.of_outside (ot.mono (o' := slot w aRm1) (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega))
      (by simp [mpTail])
  have F := Fv.trans ft
  have k := (ku.trans kv).trans kt
  have fixed (a : Nat) (ha8 : a < 8) (haN : a ∉ [aAcc, aTmp, aY])
      (har1 : a ≠ aR1) (harm : a ≠ aRm1) :
      wv t.mem B (slot w a) w = wv s.mem B (slot w a) w := by
    have hbound := h.sl (show a < 16 by omega)
    have disj (b : Nat) (hne : a ≠ b) :
        slot w a + 8 * w ≤ slot w b ∨ slot w b + 8 * (w + 2) ≤ slot w a := by
      rcases Nat.lt_or_gt_of_ne hne with hab | hba
      · have := VG.Proof.Rsa.slot_lt (w := w) hab
        left; omega
      · exact Or.inr (VG.Proof.Rsa.slot_lt hba)
    rw [ot.wv (by have := disj aRm1 harm; omega) (by omega),
      ov.wv (by have := disj aR1 har1; omega) (by omega)]
    exact ha.wv_of_not_mem ha8 haN (by omega)
  refine ⟨h.congr' F (mpTail_kmut w) k (by decide), ?_, hRm,
    (fixed aOne (by decide) (by decide) (by decide) (by decide)).trans hone,
    (fixed aR2 (by decide) (by decide) (by decide) (by decide)).trans hr2, F, k.mono (by decide)⟩
  rw [ot.wv (by simp only [slot, hdrBytes, aRm1, aR1]; omega)
    (by simp only [slot, hdrBytes, aR1]; omega)]
  exact hv

end VG.Proof.Dsa.AArch64.Generation
