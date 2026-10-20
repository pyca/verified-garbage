module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeInput
public import VerifiedGarbage.Impl.RsaKeyGen.X86_64.Candidate
public import VerifiedGarbage.Spec.Dsa
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Trial
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontAll
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.TrialLoop
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerStages

/-! # Trial division preserves the candidate and random-tape cursor -/

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
  refine WP.mono (trial_ok h.good P.dims.z hz (by have := P.dims.w4; omega)
    (by omega) h.n hn hpolicy) fun t ⟨hzf, hg, hf, hk⟩ => ?_
  have k : Keep mmRegs s t := hk.mono (by decide)
  have hn' : wv t.mem P.B (slot P.w aN) P.w = P.N := by
    rw [hf.wv_eq (by have := P.dims.w4; rng_disj)
      (by have := P.dims.z; have := h.good.scr.nowrap; simp only [slot, hdrBytes, aN] at *; omega)]
    exact h.n
  have hi := h.advance hg hn' hf k (by
    have := P.z256
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hz, by simp only [kT0, sFn]; omega, by simp only [kT1, sFn]; omega,
      by simp only [kT2, sFn]; omega⟩)
    (by
      intro j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rng_disj)
  exact ⟨hzf, hi, hf, k⟩

end VG.Proof.Dsa.X86_64.Generation
