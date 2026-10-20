module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeInput
public import VerifiedGarbage.Spec.Dsa
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Trial
import VerifiedGarbage.Proof.Dsa.Generation.Trial
import VerifiedGarbage.Proof.Framework.Omega

/-! RSA's complete trial division preserves the generation inputs and tape cursor. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64

def primeTrialRanges (w : Nat) : List (Nat × Nat) := [(slot w aTab, 2048)]

theorem primeTrial_ok {P : PrimeParams} {used : Nat} {s : State}
    (h : PrimeInput P used s) (hw : P.w ≤ 48) (hz : slot P.w aTab + 2048 ≤ P.Z)
    (hn : 8161 < P.N) (hpolicy : 1024 < Spec.Dsa.bitLength P.N ↔ 16 < P.w) :
    WP isa (seqs trial) s fun t =>
      isa.eval (.zero .x .x1) t = some (!Spec.RsaKeyGen.obviouslyComposite (Spec.Dsa.bitLength P.N) P.N) ∧
      PrimeInput P used t ∧ Frm P.B (primeTrialRanges P.w) s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.mono (VG.Proof.RsaKeyGen.AArch64.trial_ok h.ws hz P.w4 (by omega))
    fun t ⟨hflag, ht, hf, hk⟩ => ?_
  rw [h.n, VG.Proof.Dsa.Generation.trialAny_dsa hn hpolicy] at hflag
  have hn' : wv t.mem P.B (slot P.w aN) P.w = P.N := by
    rw [hf.wv_eq (by intro r hr; rw [List.mem_singleton.mp hr]; left; simp only [slot, hdrBytes, aN, aTab]; omega_arith)
      (by have := h.ws.scr.nowrap; have := h.ws.sl (show aN < 16 by decide); omega)]
    exact h.n
  have hi := h.advance ht hn' hf hk (by intro r hr; rw [List.mem_singleton.mp hr]; exact hz)
    (by
      intro j hj r hr; rw [List.mem_singleton.mp hr]
      have hj32 : j < 32 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      left; simp only [slot, hdrBytes, aTab]; omega_arith)
  refine ⟨?_, hi, hf, hk⟩
  simp only [eval, State.read, Size.bits, BitVec.setWidth_eq]
  rw [← hflag]
  simp only [bne_eq, Bool.not_not]

end VG.Proof.Dsa.AArch64.Generation
