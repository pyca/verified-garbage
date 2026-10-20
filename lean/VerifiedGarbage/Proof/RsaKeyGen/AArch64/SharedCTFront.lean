module

import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTFront

public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTBase
public import VerifiedGarbage.Proof.MillerRabin.AArch64.Kernel
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTBase
meta import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2

/-! # Constant time of RSA candidate checks with a shared round -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero eval_nonzero)
open VG.Proof.RsaKeyGen (Sched schedOf)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aY)

theorem sharedKMain_ct (M : Mont) (R : VG.Proof.MillerRabin.AArch64.Kernel)
    (hT : RelCT isa (Two TS) (seqs (montSetup M.mm ++ expSetup ++ millerRabinWith M.mm R.run ++ [mrResult])) fun _ _ => True) :
    RelCT isa (Two K0) (kMainWith M.mm R.run) fun _ _ => True := by
  unfold kMainWith
  rw [List.append_assoc]
  refine RelCT.seqs_append (by simp [loadC]) (by simp [closeCheck])
    (RelCT.seq (two_post loadC_ct fun _ _ h => loadCStage_ok h) ?_)
  -- Too close to `p`.
  refine RelCT.seqs_append (by simp [closeCheck]) (by simp)
    (RelCT.seq (two_post closeCheck_ct fun _ _ h => closeStage_ok h) ?_)
  refine two_ite (fun q s₁ s₂ h₁ h₂ => by rw [eval_nonzero, eval_nonzero, h₁.2, h₂.2])
    (finUsed2_ct fun _ _ h => h.1.1) ?_
  -- Trial division.
  refine RelCT.seqs_append (by simp [trial]) (by simp) (RelCT.seq (two_post (Ψ := fun q t =>
      (KSt q t ∧ (t.gpr .x1 != 0) = q.sch.comp) ∧ q.sch.close = false) (trial_ct fun _ _ h => h.1.1)
    fun q s h => ?_) ?_)
  · have hcl : q.sch.close = false := nonzero_false (by rw [h.1.2]; exact mask_bne _) h.2
    exact WP.mono (trialStage_ok h.1.1 hcl) fun t ht => ⟨ht, hcl⟩
  refine two_ite (fun q s₁ s₂ h₁ h₂ => by rw [eval_nonzero, eval_nonzero, h₁.1.2, h₂.1.2])
    (finUsed3_ct fun _ _ h => h.1.1.1) ?_
  -- `gcd(c − 1, e)`.
  refine RelCT.seqs_append (by simp [gcdCheck, loadE]) (by simp) (RelCT.seq (two_post (Ψ := fun q t =>
      (KSt q t ∧ (t.gpr .x3 != 0) = q.sch.gbad) ∧ q.sch.close = false ∧ q.sch.comp = false)
    (gcdCheck_ct fun _ _ h => h.1.1.1) fun q s h => ?_) ?_)
  · have hco : q.sch.comp = false := nonzero_false h.1.1.2 h.2
    exact WP.mono (gcdStage_ok h.1.1.1 h.1.2 hco) fun t ht => ⟨ht, h.1.2, hco⟩
  refine two_ite (fun q s₁ s₂ h₁ h₂ => by rw [eval_nonzero, eval_nonzero, h₁.1.2, h₂.1.2])
    (finUsed3_ct fun _ _ h => h.1.1.1) ?_
  -- Montgomery setup and Miller–Rabin.
  exact hT.mono (fun _ _ h => two_mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1, h.1.2.2, nonzero_false h.1.1.2 h.2⟩) h)
    fun _ _ h => h

end VG.Proof.RsaKeyGen.AArch64
