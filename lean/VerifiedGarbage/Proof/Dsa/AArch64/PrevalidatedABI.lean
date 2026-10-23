module

public import VerifiedGarbage.Proof.Dsa.AArch64.PrevalidatedMain
public import VerifiedGarbage.Proof.Dsa.AArch64.PrevalidatedCT
public import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingABIPost
import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingAgreement
import VerifiedGarbage.Proof.Bignum.AArch64.PcCode

/-! # The prevalidated verifier meets its shared ABI and leakage contract -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Dsa.AArch64 VG.Proof.Bignum.AArch64

theorem prevalidatedABI_of {s : State} (h : (Spec.Dsa.verifyPrevalidatedContract abi).pre s) :
    VerifyingABI s ∧ Spec.Dsa.validatePublicKeyBytes (s.gpr .x2).toNat (s.gpr .x3).toNat
      (Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) = true := by
  sig_pre [Spec.Dsa.verifyPrevalidatedContract, Spec.Dsa.verifySig, abi, argRegs, dsaVerifyStackArgs] at h
  sig_pre [Spec.Dsa.verifyPrevalidatedContract, Spec.Dsa.verifySig, abi, argRegs, dsaVerifyStackArgs] at h
  sig_split h
  exact ⟨by constructor <;> with_reducible assumption, by assumption⟩

theorem prevalidatedPre_of {s : State} (h : (Spec.Dsa.verifyContract abi).pre s)
    (hv : Spec.Dsa.validatePublicKeyBytes (s.gpr .x2).toNat (s.gpr .x3).toNat
      (Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) = true) :
    (Spec.Dsa.verifyPrevalidatedContract abi).pre s := by
  sig_pre [Spec.Dsa.verifyContract, Spec.Dsa.verifySig, abi, argRegs, dsaVerifyStackArgs] at h
  sig_pre [Spec.Dsa.verifyContract, Spec.Dsa.verifySig, abi, argRegs, dsaVerifyStackArgs] at h
  sig_pre [Spec.Dsa.verifyPrevalidatedContract, Spec.Dsa.verifySig, abi, argRegs, dsaVerifyStackArgs]
  sig_pre [Spec.Dsa.verifyPrevalidatedContract, Spec.Dsa.verifySig, abi, argRegs, dsaVerifyStackArgs]
  sig_split h
  sig_and_intros <;> with_reducible assumption

theorem prevalidatedSharedPost {s t : State} (h : VerifyingABI s) (hp : VerifyingPost h.input s t) :
    (Spec.Dsa.verifyPrevalidatedContract abi).post s t := by
  sig_post [Spec.Dsa.verifyPrevalidatedContract, Spec.Dsa.verifySig, abi, argRegs, dsaVerifyStackArgs]
  sig_post [Spec.Dsa.verifyPrevalidatedContract, Spec.Dsa.verifySig, abi, argRegs, dsaVerifyStackArgs]
  rw [hp.1, verifyStatus_u32]
  rfl

theorem prevalidatedCorrect (M : Mont)
    (s : State) (h : (Spec.Dsa.verifyPrevalidatedContract abi).pre s) :
    ∃ trace t, Exec isa (Prevalidated.verify M.mm) s trace t ∧ abiPreserved s t ∧
      (Spec.Dsa.verifyPrevalidatedContract abi).post s t := by
  obtain ⟨ha, hv⟩ := prevalidatedABI_of h
  obtain ⟨trace, t, he, hp⟩ := prevalidatedMain_ok M ha.pre hv
  exact ⟨trace, t, he, abiPreserved_of_keep hp.2.2, prevalidatedSharedPost ha hp⟩

theorem prevalidatedConstantTime (M : Mont) : ConstantTime isa (Spec.Dsa.verifyPrevalidatedContract abi).pre
    (Spec.Dsa.verifyPrevalidatedContract abi).pub (Prevalidated.verify M.mm) := by
  intro s₁ s₂ trace₁ trace₂ t₁ t₂ h₁ h₂ hp e₁ e₂
  change (Spec.Dsa.verifyContract abi).pub s₁ s₂ at hp
  exact (prevalidatedMain_ct M _ _ _ _ _ _
    (verifyingPublicRelated (prevalidatedABI_of h₁).1 (prevalidatedABI_of h₂).1 hp) e₁ e₂).1

end VG.Proof.Dsa.AArch64
