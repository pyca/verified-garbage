module

public import VerifiedGarbage.Proof.Ffdh.Arm.SharedCheckPublicPrograms
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Ffdh.Arm.SharedCheckPublicCorrect
import VerifiedGarbage.Proof.Ffdh.Arm.SharedCheckPublicContractCT
import VerifiedGarbage.Proof.Ffdh.Arm.SharedCheckPublicSat

/-! Shared callable arithmetic retains the existing public-validation contract. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem sharedCheckPublic_verified (b : MontBackend) :
    Verified target (SharedCheckPublic.code b) (Spec.Ffdh.checkPublicContract abi 176) :=
  ⟨sharedCheckPublic_correct b, sharedCheckPublic_contract_ct b, sharedCheckPublic_sat⟩

end VG.Proof.Ffdh.Arm
