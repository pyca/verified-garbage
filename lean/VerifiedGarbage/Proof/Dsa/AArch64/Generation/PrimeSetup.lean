module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PrimeSetup
public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.MontPrep
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrSq
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrShift
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Rsa.Ranges
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Close
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Dsa.AArch64.Setup
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MontSetup

/-! ### `Dsa.AArch64.Generation.PrimeR2`, which this module and modules that import it used -/

section

/-! Prepare R² and the inverse without a nonzero-top-limb assumption. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.RsaKeyGen.AArch64 VG.Proof.Ffdh.AArch64.ParameterCandidate
open VG.Proof.MlKem.AArch64 (Keep)

theorem primeR2_ok (M : Mont) {s : State} {B : Addr} {Z w N : Nat}
    (h : Ws s B Z w) (hw48 : w ≤ 48)
    (hn : wv s.mem B (slot w aN) w = N) (hodd : N % 2 = 1) (hN1 : 1 < N) :
    WP isa (Impl.Dsa.AArch64.Generation.primeR2 M.mm) s fun t =>
      Ws t B Z w ∧
      ((word t.mem B (slot w aN)).toNat * (word t.mem B (8 * sMinv)).toNat + 1) % 2 ^ 64 = 0 ∧
      wv t.mem B (slot w aN) w = N ∧
      wv t.mem B (slot w aOne) w = 1 ∧
      wv t.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % N ∧
      Frm B (mpRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hnw := h.scr.nowrap
  have hZ := h.hZ
  have hZ16 : 256 + 16 * (8 * (w + 2)) ≤ Z := by simpa only [slot, hdrBytes] using hZ
  have hodd0 : (word s.mem B (slot w aN)).toNat % 2 = 1 := by
    have e := wv_add s.mem B (slot w aN) 1 (w - 1)
    rw [show 1 + (w - 1) = w by have := h.w1; omega_using [this], hn] at e
    simp only [wv, Nat.mul_zero, Nat.add_zero, Nat.zero_add] at e
    omega
  unfold Impl.Dsa.AArch64.Generation.primeR2
  refine WP.seq (WP.mono (msHead_ok h hodd0) fun u ⟨⟨hinv, hm, _, _, _⟩, ku⟩ => ?_)
  have ou : Outside B (8 * sMinv) 8 s.mem u.mem := by
    rw [hm]; exact writeW_outside _ _ _ (by simp only [sMinv]; omega_using [])
  have fu : Frm B (mpRanges w) s.mem u.mem := Frm.of_outside ou (by simp [mpRanges])
  have hu : Ws u B Z w := h.congr' fu (mpRanges_kmut w) ku (by decide)
  have hnu : wv u.mem B (slot w aN) w = N := by
    rw [ou.wv (by simp only [slot, hdrBytes, aN, sMinv]; omega_using [])
      (by simp only [slot, hdrBytes, aN]; omega_using [hw48])]; exact hn
  have hword : word u.mem B (slot w aN) = word s.mem B (slot w aN) :=
    ou.word (by simp only [slot, hdrBytes, aN, sMinv]; omega_using [])
      (by simp only [slot, hdrBytes, aN]; omega_using [])
  refine WP.mono (constants_ok M hu.good.1 hu.good.2 h.w1 hw48 hnu hN1 hodd
    (by rw [hword]; exact hinv)) fun t ⟨_, hone, hr2, ft, kt⟩ => ?_
  have ft' : Frm B (mpTail w) u.mem t.mem := ft.mono (by simp [mpTail, r2Ranges])
  obtain ⟨he, hw, hv⟩ := mp_fix ft' hnw hZ
  refine ⟨hu.congr' ft' (mpTail_kmut w) kt (by decide), ?_, hv.trans hnu, hone, ?_,
    fu.trans (ft'.mono fun r hr => List.mem_cons_of_mem _ hr), (ku.trans kt).mono (by decide)⟩
  · rw [hw, he, hword]; exact hinv
  · rw [← Nat.pow_add, show 64 * w + 64 * w = 128 * w by omega_using []]
    exact hr2

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! ### `Dsa.AArch64.Generation.PrimeConstants`, which this module and modules that import it used -/

section

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
  have hw' : w < 2 ^ 31 := by have := h.w2; omega_arith
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
    Frm.of_outside (ov.mono (o' := slot w aR1) (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega_arith))
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
    have hm := Nat.mod_lt (2 ^ (64 * w)) (show 0 < N by omega_arith)
    cases hc : (!t.c) <;> rw [hc] at ht <;>
      simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at ht <;> omega_arith
  have ft : Frm B (mpTail w) v.mem t.mem :=
    Frm.of_outside (ot.mono (o' := slot w aRm1) (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega_arith))
      (by simp [mpTail])
  have F := Fv.trans ft
  have k := (ku.trans kv).trans kt
  have fixed (a : Nat) (ha8 : a < 8) (haN : a ∉ [aAcc, aTmp, aY])
      (har1 : a ≠ aR1) (harm : a ≠ aRm1) :
      wv t.mem B (slot w a) w = wv s.mem B (slot w a) w := by
    have hbound := h.sl (show a < 16 by omega_arith)
    have disj (b : Nat) (hne : a ≠ b) :
        slot w a + 8 * w ≤ slot w b ∨ slot w b + 8 * (w + 2) ≤ slot w a := by
      rcases Nat.lt_or_gt_of_ne hne with hab | hba
      · have := VG.Proof.Rsa.slot_lt (w := w) hab
        left; omega_arith
      · exact Or.inr (VG.Proof.Rsa.slot_lt hba)
    rw [ot.wv (by have := disj aRm1 harm; omega_arith) (by omega_arith),
      ov.wv (by have := disj aR1 har1; omega_arith) (by omega_arith)]
    exact ha.wv_of_not_mem ha8 haN (by omega_arith)
  refine ⟨h.congr' F (mpTail_kmut w) k (by decide), ?_, hRm,
    (fixed aOne (by decide) (by decide) (by decide) (by decide)).trans hone,
    (fixed aR2 (by decide) (by decide) (by decide) (by decide)).trans hr2, F, k.mono (by decide)⟩
  rw [ot.wv (by simp only [slot, hdrBytes, aRm1, aR1]; omega_arith)
    (by simp only [slot, hdrBytes, aR1]; omega_arith)]
  exact hv

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! Establish every modulus-dependent input to the shared Miller–Rabin round. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.RsaKeyGen.AArch64 VG.Proof.Ffdh.AArch64.ParameterCandidate
open VG.Proof.MlKem.AArch64 (Keep)

structure ModulusReady (s : State) (B : Addr) (Z w N : Nat) : Prop where
  ws : Ws s B Z w
  inverse : ((word s.mem B (slot w aN)).toNat * (word s.mem B (8 * sMinv)).toNat + 1) % 2 ^ 64 = 0
  modulus : wv s.mem B (slot w aN) w = N
  one : wv s.mem B (slot w aOne) w = 1
  r2 : wv s.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % N
  r1 : wv s.mem B (slot w aR1) w = 2 ^ (64 * w) % N
  rm1 : wv s.mem B (slot w aRm1) w = N - 2 ^ (64 * w) % N
  exponent : ECtx s.mem B w N

def modulusRanges (w : Nat) : List (Nat × Nat) :=
  mpRanges w ++ [(slot w aE, 8 * (w + 1))]

theorem primeSetup_ok (M : Mont) {s : State} {B : Addr} {Z w N : Nat}
    (h : Ws s B Z w) (hw48 : w ≤ 48) (hEZ : slot w aE + 8 * (w + 2) ≤ Z)
    (hn : wv s.mem B (slot w aN) w = N) (hodd : N % 2 = 1) (hN1 : 1 < N) :
    WP isa (Impl.Dsa.AArch64.Generation.primeSetup M.mm) s fun t =>
      ModulusReady t B Z w N ∧ Frm B (modulusRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hnw := h.scr.nowrap
  have hZ := h.hZ
  have hz64 : Z ≤ 2 ^ 64 := by omega_using [hnw]
  unfold Impl.Dsa.AArch64.Generation.primeSetup
  refine WP.seq (WP.mono (primeR2_ok M h hw48 hn hodd hN1)
    fun u ⟨hu, hinv, hnu, hone, hr2, fu, ku⟩ => ?_)
  refine wp_seqs_append (by simp [Impl.Dsa.AArch64.Generation.primeConstants])
    (by simp [expSetup, lowWord]) ?_
  refine WP.mono (primeConstants_ok M hu hnu hodd hN1 hinv hone hr2)
    fun v ⟨hv, hr1, hrm1, honev, hr2v, fv, kv⟩ => ?_
  obtain ⟨hmi, hn0, hnv⟩ := mp_fix fv hnw hZ
  have hinvv : ((word v.mem B (slot w aN)).toNat * (word v.mem B (8 * sMinv)).toNat + 1) % 2 ^ 64 = 0 := by
    rw [hmi, hn0]; exact hinv
  refine WP.mono (expSetup_ok hv hEZ (hnv.trans hnu) hodd hN1)
    fun t ⟨he, fe, ht, kt⟩ => ?_
  have fixed (a : Nat) (ha : a < 16) : wv t.mem B (slot w a) w = wv v.mem B (slot w a) w := by
    have hh : slot w a + 8 * (w + 2) ≤ slot w aE := VG.Proof.Rsa.slot_lt (by unfold aE; omega_using [ha])
    exact fe.wv_eq (by simp only [List.mem_singleton]; rintro r rfl; left; omega_using [hh])
      (by omega_using [hEZ, hnw, hh])
  have fixedWord (d : Nat) (hd : d + 8 ≤ slot w aE) : word t.mem B d = word v.mem B d :=
    fe.word_eq (by simp only [List.mem_singleton]; rintro r rfl; exact Or.inl hd) (by omega_using [hEZ, hnw, hd])
  refine ⟨⟨ht, ?_, (fixed aN (by decide)).trans (hnv.trans hnu),
      (fixed aOne (by decide)).trans honev, (fixed aR2 (by decide)).trans hr2v,
      (fixed aR1 (by decide)).trans hr1, (fixed aRm1 (by decide)).trans hrm1, he⟩,
    ?_, ((ku.trans kv).trans kt).mono (by decide)⟩
  · rw [fixedWord (slot w aN) (by simp only [slot, hdrBytes, aN, aE]; omega_using []),
      fixedWord (8 * sMinv) (by simp only [slot, hdrBytes, aE, sMinv]; omega_using [])]
    exact hinvv
  · exact ((fu.trans (fv.mono fun r hr => List.mem_cons_of_mem _ hr)).mono
      fun r hr => List.mem_append_left _ hr).trans
      (fe.mono fun r hr => List.mem_append_right _ hr)

end VG.Proof.Dsa.AArch64.Generation
