module
public import VerifiedGarbage.Proof.MillerRabin.AArch64.Kernel
public import VerifiedGarbage.Impl.RsaKeyGen.AArch64.Candidate
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.Table

import VerifiedGarbage.Proof.RsaKeyGen.AArch64.SharedKMain
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Code

/-! # Correctness of the RSA candidate calling shared Miller–Rabin -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

/-- `vg_rsa_keygen_candidate` ends as the specification says. -/
theorem sharedCode_correct (M : Mont) (R : VG.Proof.MillerRabin.AArch64.Kernel) (s : State) (h : candContract.pre s) :
    ∃ t s', Exec isa (codeWith M.mm R.run) s t s' ∧ abiPreserved s s' ∧ candContract.post s s' := by
  have c := kctx_of h
  suffices hwp : WP isa (codeWith M.mm R.run) s fun s' => abiPreserved s s' ∧ candPost s s' by
    obtain ⟨t, s', he, hg, hp⟩ := hwp
    exact ⟨t, s', he, hg, hp⟩
  have hk1 := c.k1
  have hk8 := c.k8
  obtain ⟨w, hw⟩ : ∃ w, (s.gpr .x1).toNat = 8 * w := ⟨(s.gpr .x1).toNat / 8, by omega⟩
  unfold codeWith
  simp only [seqs]
  refine WP.seq (WP.mono (entry_ok c) fun t₁ he => ?_)
  refine WP.seq (WP.mono (zeros_ok c he) fun t₂ hz => ?_)
  refine WP.seq (WP.mono (lenCheck_ok c he hz) fun t₄ hf => ?_)
  refine WP.ite (!decide ((s.gpr .x1).toNat ≤ (stackArg s 0).toNat))
    (by rw [eval_zero, hf.x5]; cases decide ((s.gpr .x1).toNat ≤ (stackArg s 0).toNat) <;> rfl)
    (fun hlt => ?_) (fun hlt => ?_)
  · simp only [Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_le] at hlt
    exact front_none c hf hlt
  · simp only [Bool.not_eq_false', decide_eq_true_eq] at hlt
    refine WP.mono (sharedKMain_ok M R (mainCtx_of c hf hw hlt)) fun t ht => candEnd_post hf.zero hf.keep ?_
    rw [candRes_main hw (by omega) hlt, hw]
    exact ht

end VG.Proof.RsaKeyGen.AArch64
