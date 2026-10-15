module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Constants
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrShift
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontAll
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.Omega

/-! # FFDH parameter candidates on x86-64: a prepared shared Miller–Rabin modulus -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.RsaKeyGen.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- All modulus-dependent data needed to call the shared round with any witness. -/
structure ModulusReady (s : State) (B : Addr) (Z w : Nat) (mi : BitVec 64) (N : Nat) : Prop where
  good : Good s B Z w mi
  inv : ((word s.mem B (slot w aN)).toNat * mi.toNat + 1) % 2 ^ 64 = 0
  n : wv s.mem B (slot w aN) w = N
  r2 : wv s.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % N
  r1 : wv s.mem B (slot w aR1) w = 2 ^ (64 * w) % N
  rm1 : wv s.mem B (slot w aRm1) w = N - 2 ^ (64 * w) % N
  exponent : ECtx s.mem B w N

def modulusRanges (w : Nat) : List (Nat × Nat) :=
  prepareRanges w ++ constantRanges w ++ [(slot w aE, 8 * (w + 1))]

theorem prepareModulus_ok (M : Mont) (R : R2Impl M) {s : State} {B : Addr} {Z w N : Nat} {mi : BitVec 64}
    (hg : Good s B Z w mi) (hd : MrDims B Z w)
    (hn : wv s.mem B (slot w aN) w = N) (hodd : N % 2 = 1) (hN1 : 1 < N)
    (hlo : 2 ^ (64 * (w - 1)) ≤ N) :
    WP isa (prepareModulus M.mm R.code) s fun t => ∃ mi', ModulusReady t B Z w mi' N ∧
      Frm B (modulusRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hw : w < 2 ^ 31 := by have := hd.w128; omega
  have hz64 : Z ≤ 2 ^ 64 := Nat.le_trans (Nat.le_add_left Z B.toNat) hg.scr.nowrap
  have hNread : slot w aN + 8 * w ≤ 2 ^ 64 := by
    have he := slot_le (w := w) (show aN < 8 by decide)
    omega_using [he, hd.z, hz64]
  have hNword : slot w aN + 8 ≤ 2 ^ 64 := by omega_using [hNread, hd.w4]
  have hR2read : slot w aR2 + 8 * w ≤ 2 ^ 64 := by
    have he := slot_le (w := w) (show aR2 < 8 by decide)
    omega_using [he, hd.z, hz64]
  have hR1read : slot w aR1 + 8 * w ≤ 2 ^ 64 := by
    have he := hd.x
    simp only [slot, aR1, aRm1] at he ⊢
    omega_using [he, hz64]
  have hRm1read : slot w aRm1 + 8 * w ≤ 2 ^ 64 := by omega_using [hd.x, hz64]
  unfold prepareModulus
  refine WP.seq (WP.mono (prepareR2_ok M R hg hd.z (by have := hd.w4; omega)
    (by have := hd.w128; omega) hn hodd hlo) fun u ⟨mi', hgu, hinv, hnu, hone, hr2, _, hf, ku⟩ => ?_)
  refine WP.seq (WP.mono (prepareConstants_ok M hgu hd.z hd.x (by have := hd.w4; omega) hw hnu hinv hone hodd hN1 hr2)
    fun v ⟨hgv, hr1, hrm1, hf', kv⟩ => ?_)
  have hnv : wv v.mem B (slot w aN) w = N := by
    rw [hf'.wv_eq (by simp only [constantRanges]; rng_disj) hNread]
    exact hnu
  have hinvv : ((word v.mem B (slot w aN)).toNat * mi'.toNat + 1) % 2 ^ 64 = 0 := by
    rw [hf'.word_eq (by simp only [constantRanges]; rng_disj) hNword]
    exact hinv
  have hr2v : wv v.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % N := by
    rw [hf'.wv_eq (by simp only [constantRanges]; rng_disj) hR2read]
    exact hr2
  refine WP.mono (expSetup_ok hgv hd hnv hodd hN1) fun t ⟨he, hfe, hgt, kt⟩ => ?_
  refine ⟨mi', ⟨hgt, ?_, ?_, ?_, ?_, ?_, he⟩, (hf.append hf').append hfe,
    ((ku.trans kv).trans kt).mono (by decide)⟩
  · rw [hfe.word_eq (by rng_disj) hNword]; exact hinvv
  · rw [hfe.wv_eq (by rng_disj) hNread]; exact hnv
  · rw [hfe.wv_eq (by rng_disj) hR2read]; exact hr2v
  · rw [hfe.wv_eq (by rng_disj) hR1read]; exact hr1
  · rw [hfe.wv_eq (by rng_disj) hRm1read]; exact hrm1

end VG.Proof.Ffdh.X86_64.ParameterCandidate
