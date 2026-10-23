module

import VerifiedGarbage.Proof.Dsa.AArch64.PrevalidatedABI
public import VerifiedGarbage.Proof.Dsa.AArch64.PrevalidatedSat
public import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingVerified
public import VerifiedGarbage.Impl.Dsa.AArch64.Prevalidated
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Proof.Dsa.AArch64.CallHeadCT
public import VerifiedGarbage.Proof.Dsa.AArch64.CoreSign
public import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleCTState
public import VerifiedGarbage.Proof.Dsa.AArch64.SignReleaseCT
public import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingPublic
public import VerifiedGarbage.Proof.Dsa.AArch64.WorkspaceBridge
public import VerifiedGarbage.Spec.Dsa.Prevalidated

/-! # Verified DSA signature checking under the merged immutable-key precondition -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Dsa.AArch64 VG.Proof.Bignum.AArch64

def prevalidatedSatState : State where
  gpr := (verifyingSatState).gpr
  sp := (verifyingSatState).sp
  rd := (verifyingSatState).rd
  wr := (verifyingSatState).wr
  mem a := if 0x2000 ≤ a.toNat ∧ a.toNat < 0x2194 then
    validatedSatKey[a.toNat - 0x2000]?.getD 0 else (verifyingSatState).mem a

theorem prevalidatedSatisfiable : ∃ s, (Spec.Dsa.verifyPrevalidatedContract abi).pre s := by
  have hb : Spec.Rsa.bytesAt (prevalidatedSatState).mem 0x2000 404 = validatedSatKey := by
    decide +kernel
  have hv : Spec.Dsa.validatePublicKeyBytes 128 20
      (Spec.Rsa.bytesAt (prevalidatedSatState).mem 0x2000 404) = true := by
    rw [hb]; exact validatedSatKey_valid
  have ho : ∃ s, (Spec.Dsa.verifyContract abi).pre s ∧ s = prevalidatedSatState := by
    refine ⟨prevalidatedSatState, ?_, rfl⟩
    sig_pre [Spec.Dsa.verifyContract, Spec.Dsa.verifySig, abi, argRegs, dsaVerifyStackArgs]
    sig_and_intros
    all_goals first
      | rfl
      | decide
      | exact Region.disjoint_of_sep (by decide)
      | (intro a h₁ h₂
         sig_simp_only [Region.Contains, prevalidatedSatState, verifyingSatState,
           stackArg, stackArgAddr, Mem.readW, Mem.read] at h₁ h₂
         bv_omega)
  refine ⟨prevalidatedSatState, prevalidatedPre_of ?_ hv⟩
  obtain ⟨s, h, rfl⟩ := ho
  exact h

theorem prevalidated_verified (M : Mont) :
    Verified target (Prevalidated.verify M.mm) (Spec.Dsa.verifyPrevalidatedContract abi) :=
  ⟨prevalidatedCorrect M, prevalidatedConstantTime M, prevalidatedSatisfiable⟩

end VG.Proof.Dsa.AArch64
