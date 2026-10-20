module
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PrimeSetup
public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.MontPrep
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrSq

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeConstants
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrShift
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeR2
import VerifiedGarbage.Proof.Rsa.Ranges

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
  have hz64 : Z ≤ 2 ^ 64 := by omega
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
    have hh : slot w a + 8 * (w + 2) ≤ slot w aE := VG.Proof.Rsa.slot_lt (by unfold aE; omega)
    exact fe.wv_eq (by simp only [List.mem_singleton]; rintro r rfl; left; omega)
      (by omega)
  have fixedWord (d : Nat) (hd : d + 8 ≤ slot w aE) : word t.mem B d = word v.mem B d :=
    fe.word_eq (by simp only [List.mem_singleton]; rintro r rfl; exact Or.inl hd) (by omega)
  refine ⟨⟨ht, ?_, (fixed aN (by decide)).trans (hnv.trans hnu),
      (fixed aOne (by decide)).trans honev, (fixed aR2 (by decide)).trans hr2v,
      (fixed aR1 (by decide)).trans hr1, (fixed aRm1 (by decide)).trans hrm1, he⟩,
    ?_, ((ku.trans kv).trans kt).mono (by decide)⟩
  · rw [fixedWord (slot w aN) (by simp only [slot, hdrBytes, aN, aE]; omega),
      fixedWord (8 * sMinv) (by simp only [slot, hdrBytes, aE, sMinv]; omega)]
    exact hinvv
  · exact ((fu.trans (fv.mono fun r hr => List.mem_cons_of_mem _ hr)).mono
      fun r hr => List.mem_append_left _ hr).trans
      (fe.mono fun r hr => List.mem_append_right _ hr)

end VG.Proof.Dsa.AArch64.Generation
