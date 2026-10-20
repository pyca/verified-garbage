module

public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTCode
public import VerifiedGarbage.Proof.MillerRabin.AArch64.Kernel

meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Code
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTBase
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2

/-! # Constant time of the RSA candidate calling shared Miller–Rabin -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Proof.RsaKeyGen (Sched schedOf)

theorem sharedCode_ct (M : Mont) (R : VG.Proof.MillerRabin.AArch64.Kernel) (hK : RelCT isa (Two K0) (kMainWith M.mm R.run) fun _ _ => True) :
    RelCT isa (Two CRel) (codeWith M.mm R.run) fun _ _ => True := by
  unfold codeWith
  simp only [seqs]
  refine RelCT.seq entry_ct (RelCT.seq zeros_ct (RelCT.seq lenCheck_ct ?_))
  refine two_ite (fun q s₁ s₂ h₁ h₂ => by rw [eval_zero, eval_zero, h₁.x5, h₂.x5]) ?_ ?_
  · exact finNone_ct fun _ _ h => h.1
  · exact hK.mono (fun _ _ h => two_bind (fun q t₁ t₂ h₁ h₂ => ⟨q, h₁.1.k0 (by
        have := h₁.2; rw [eval_zero, h₁.1.x5] at this; revert this
        cases hd : decide (8 * q.w ≤ q.rl) <;> simp_all), h₂.1.k0 (by
        have := h₂.2; rw [eval_zero, h₂.1.x5] at this; revert this
        cases hd : decide (8 * q.w ≤ q.rl) <;> simp_all)⟩) h) fun _ _ h => h
theorem sharedCode_constantTime (M : Mont) (R : VG.Proof.MillerRabin.AArch64.Kernel) (hK : RelCT isa (Two K0) (kMainWith M.mm R.run) fun _ _ => True) :
    ConstantTime isa candPre candPub (codeWith M.mm R.run) :=
  RelCT.constantTime ((sharedCode_ct M R hK).mono (fun s₁ _ ⟨h₁, h₂, hp⟩ =>
    ⟨cpubOf s₁, crel_self h₁, crel_of h₁ h₂ hp, hp.2.1⟩) fun _ _ h => h)

end VG.Proof.RsaKeyGen.AArch64
