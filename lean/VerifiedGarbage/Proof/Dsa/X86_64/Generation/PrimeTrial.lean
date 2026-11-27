module

public import VerifiedGarbage.Impl.RsaKeyGen.X86_64.Candidate
public import VerifiedGarbage.Spec.Dsa
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontAll
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeFrame
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerStages
import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.TrialLoop
import VerifiedGarbage.Proof.Dsa.Generation.Trial
import VerifiedGarbage.Spec.RsaKeyGen
import Aesop.BuiltinRules
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeState
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PrimeSetup
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Prepared
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeR2
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrShift
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SourceFrame

/-! ### `Dsa.X86_64.Generation.PrimeInput`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.Generation.PrimeSetup`, which only this module used -/

section

/-! # Prepare every modulus-dependent value for the callable Miller–Rabin round -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.RsaKeyGen.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64.ParameterCandidate

theorem primeSetup_ok (M : Mont) {s : State} {B : Addr} {Z w N : Nat} {mi : BitVec 64}
    (hg : Good s B Z w mi) (hd : MrDims B Z w)
    (hn : wv s.mem B (slot w aN) w = N) (hodd : N % 2 = 1) (hN1 : 1 < N)
    (hw48 : w ≤ 48) :
    WP isa (Impl.Dsa.X86_64.Generation.primeSetup M.mm) s fun t => ∃ mi', ModulusReady t B Z w mi' N ∧
      Frm B (modulusRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hw : w < 2 ^ 31 := by have := hd.w128; omega_using [hw48]
  have hz64 : Z ≤ 2 ^ 64 := Nat.le_trans (Nat.le_add_left Z B.toNat) hg.scr.nowrap
  have hNread : slot w aN + 8 * w ≤ 2 ^ 64 := by
    have he := slot_le (w := w) (show aN < 8 by decide)
    omega_using [he, hd.z, hz64]
  have hNword : slot w aN + 8 ≤ 2 ^ 64 := by omega_using [hNread, hd.w4]
  have hOneread : slot w aOne + 8 * w ≤ 2 ^ 64 := by
    have he := slot_le (w := w) (show aOne < 8 by decide)
    omega_using [he, hd.z, hz64]
  have hR2read : slot w aR2 + 8 * w ≤ 2 ^ 64 := by
    have he := slot_le (w := w) (show aR2 < 8 by decide)
    omega_using [he, hd.z, hz64]
  have hR1read : slot w aR1 + 8 * w ≤ 2 ^ 64 := by
    have he := hd.x
    simp only [slot, aR1, aRm1] at he ⊢
    omega_using [he, hz64]
  have hRm1read : slot w aRm1 + 8 * w ≤ 2 ^ 64 := by omega_using [hd.x, hz64]
  unfold Impl.Dsa.X86_64.Generation.primeSetup
  refine WP.seq (WP.mono (primeR2_ok M hg hd.z (by have := hd.w4; omega_using [this]) hw48 hn hodd hN1) fun u ⟨mi', hgu, hinv, hnu, hone, hr2, _, hf, ku⟩ => ?_)
  refine WP.seq (WP.mono (prepareConstants_ok M hgu hd.z hd.x (by have := hd.w4; omega_using [this]) hw hnu hinv hone hodd hN1 hr2)
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
  refine ⟨mi', ⟨hgt, ?_, ?_, ?_, ?_, ?_, ?_, he⟩, (hf.append hf').append hfe,
    ((ku.trans kv).trans kt).mono (by decide)⟩
  · rw [hfe.word_eq (by rng_disj) hNword]; exact hinvv
  · rw [hfe.wv_eq (by rng_disj) hNread]; exact hnv
  · rw [hfe.wv_eq (by rng_disj) hOneread, hf'.wv_eq (by simp only [constantRanges]; rng_disj) hOneread]
    exact hone
  · rw [hfe.wv_eq (by rng_disj) hR2read]; exact hr2v
  · rw [hfe.wv_eq (by rng_disj) hR1read]; exact hr1
  · rw [hfe.wv_eq (by rng_disj) hRm1read]; exact hrm1

end VG.Proof.Dsa.X86_64.Generation

end

end


/-! # Preserved arguments around modulus preparation -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaKeyGen.X86_64 VG.Proof.Ffdh.X86_64.ParameterCandidate

structure PrimeInput (P : PrimeParams) (mi : BitVec 64) (used : Nat) (s : State) : Prop where
  good : Good s P.B P.Z P.w mi
  n : wv s.mem P.B (slot P.w aN) P.w = P.N
  ptr : word s.mem P.B (8 * kOut) = P.p
  len : word s.mem P.B (8 * kUsedP) = BitVec.ofNat 64 P.len
  draw : word s.mem P.B (8 * kLen) = BitVec.ofNat 64 P.drawBytes
  rand : word s.mem P.B (8 * kRand) = P.rp
  randLen : word s.mem P.B (8 * kRandLen) = BitVec.ofNat 64 P.rand.length
  used : word s.mem P.B (8 * kUsed) = BitVec.ofNat 64 used
  checks : word s.mem P.B (8 * kChecks) = BitVec.ofNat 64 P.checks
  source : Src s P.B P.Z P.rp P.rand
  writable : ∀ i < P.len, InRegions s.wr (off P.p i) 1
  stack : s.gpr .rsp = P.sp

theorem PrimeState.input {P : PrimeParams} {mi : BitVec 64} {used : Nat} {s : State}
    (h : PrimeState P mi used s) : PrimeInput P mi used s :=
  ⟨h.ready.good, h.ready.n, h.ptr, h.len, h.draw, h.rand, h.randLen, h.used, h.checks,
    h.source, h.writable, h.stack⟩

theorem PrimeInput.advance {P : PrimeParams} {mi mi' : BitVec 64} {used : Nat} {s t : State}
    {rs : List (Nat × Nat)} (h : PrimeInput P mi used s)
    (hg : Good t P.B P.Z P.w mi') (hn : wv t.mem P.B (slot P.w aN) P.w = P.N)
    (hf : Frm P.B rs s.mem t.mem) (hk : Keep mmRegs s t)
    (hr : ∀ r ∈ rs, r.1 + r.2 ≤ P.Z)
    (hh : ∀ k ∈ [kOut, kUsedP, kLen, kRand, kRandLen, kUsed, kChecks], ∀ r ∈ rs,
      8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k) : PrimeInput P mi' used t := by
  have hword : ∀ k ∈ [kOut, kUsedP, kLen, kRand, kRandLen, kUsed, kChecks],
      word t.mem P.B (8 * k) = word s.mem P.B (8 * k) := by
    intro k hmem
    have hk32 : k < 32 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact hf.word_eq (hh k hmem) (by omega_using [hk32])
  refine ⟨hg, hn, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hword kOut (by simp)).trans h.ptr
  · exact (hword kUsedP (by simp)).trans h.len
  · exact (hword kLen (by simp)).trans h.draw
  · exact (hword kRand (by simp)).trans h.rand
  · exact (hword kRandLen (by simp)).trans h.randLen
  · exact (hword kUsed (by simp)).trans h.used
  · exact (hword kChecks (by simp)).trans h.checks
  · exact source_of_work h.source (extra := []) hf.work hr (by simp) P.randMax hk
  · intro i hi; rw [hk.2.2]; exact h.writable i hi
  · exact (hk.gpr (by decide)).trans h.stack

theorem primeInputSetup_ok (M : Mont) {P : PrimeParams} {mi : BitVec 64} {used : Nat} {s : State}
    (h : PrimeInput P mi used s) (hw : P.w ≤ 48) :
    WP isa (Impl.Dsa.X86_64.Generation.primeSetup M.mm) s fun t =>
      ∃ mi', PrimeState P mi' used t ∧ Frm P.B (modulusRanges P.w) s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.mono (primeSetup_ok M h.good P.dims h.n P.odd (by have := P.n3; omega_using [this]) hw)
    fun t ⟨mi', ht, hf, hk⟩ => ?_
  have hi := h.advance ht.good ht.n hf hk (by
    have hroom := P.room
    simp only [modulusRanges, prepareRanges, constantRanges, r2Ranges, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros <;>
      simp only [slot, hdrBytes, aAcc, aTmp, aOne, aR2, aY, aR1, aRm1, aE, sMinv, sCnt, sFn] at hroom ⊢ <;> omega_using [hroom])
    (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [modulusRanges, prepareRanges, constantRanges, r2Ranges, List.cons_append, List.nil_append, sCnt] <;> rng_disj)
  exact ⟨mi', ⟨ht, hi.ptr, hi.len, hi.draw, hi.rand, hi.randLen, hi.used, hi.checks,
    hi.source, hi.writable, hi.stack⟩, hf, hk⟩

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # Trial division preserves the candidate and random-tape cursor -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/Trial.lean`, which only this module imported.
section

/-! # DSA uses RSA's complete native small-prime table and trial loop -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem trial_ok {s : State} {B : Addr} {Z w c bits : Nat} {mi : BitVec 64}
    (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z) (hTZ : slot w aTab + 2048 ≤ Z)
    (hw : 1 ≤ w) (hw64 : w ≤ 64) (hc : wv s.mem B (slot w aN) w = c)
    (hcgt : 8161 < c) (hpolicy : 1024 < bits ↔ 16 < w) :
    WP isa (seqs trial) s fun t =>
      t.zf = some (!Spec.RsaKeyGen.obviouslyComposite bits c) ∧ Good t B Z w mi ∧
      Frm B [(slot w aTab, 2048), (8 * kT0, 8), (8 * kT1, 8), (8 * kT2, 8)] s.mem t.mem ∧
      Keep [.rax, .rbx, .rcx, .rdx, .rsi, .rbp, .r8, .r12, .r13, .r14, .r15] s t := by
  refine WP.mono (VG.Proof.RsaKeyGen.X86_64.trial_ok hg hZ hTZ hw hw64) fun t ⟨hz, ht⟩ => ?_
  rw [hc, VG.Proof.Dsa.Generation.trialAny_dsa hcgt hpolicy] at hz
  exact ⟨hz, ht⟩

end VG.Proof.Dsa.X86_64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaKeyGen.X86_64

def primeTrialRanges (w : Nat) : List (Nat × Nat) :=
  [(slot w aTab, 2048), (8 * kT0, 8), (8 * kT1, 8), (8 * kT2, 8)]

theorem primeTrial_ok {P : PrimeParams} {mi : BitVec 64} {used : Nat} {s : State}
    (h : PrimeInput P mi used s) (hw : P.w ≤ 48) (hz : slot P.w aTab + 2048 ≤ P.Z)
    (hn : 8161 < P.N) (hpolicy : 1024 < Spec.Dsa.bitLength P.N ↔ 16 < P.w) :
    WP isa (seqs trial) s fun t =>
      t.zf = some (!Spec.RsaKeyGen.obviouslyComposite (Spec.Dsa.bitLength P.N) P.N) ∧
      PrimeInput P mi used t ∧ Frm P.B (primeTrialRanges P.w) s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.mono (trial_ok h.good P.dims.z hz (by have := P.dims.w4; omega_using [this])
    (by omega_using [hw]) h.n hn hpolicy) fun t ⟨hzf, hg, hf, hk⟩ => ?_
  have k : Keep mmRegs s t := hk.mono (by decide)
  have hn' : wv t.mem P.B (slot P.w aN) P.w = P.N := by
    rw [hf.wv_eq (by have := P.dims.w4; rng_disj)
      (by have := P.dims.z; have := h.good.scr.nowrap; simp only [slot, hdrBytes, aN] at *; omega_using [hw])]
    exact h.n
  have hi := h.advance hg hn' hf k (by
    have := P.z256
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hz, by simp only [kT0, sFn]; omega_using [hz], by simp only [kT1, sFn]; omega_using [hz],
      by simp only [kT2, sFn]; omega_using [hz]⟩)
    (by
      intro j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rng_disj)
  exact ⟨hzf, hi, hf, k⟩

end VG.Proof.Dsa.X86_64.Generation
