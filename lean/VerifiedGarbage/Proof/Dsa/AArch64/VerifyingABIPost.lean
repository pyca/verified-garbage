module
public import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingABI
public import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingReturn

import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingABIPre
import VerifiedGarbage.Proof.Bignum.AArch64.PcCode
import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingMain

/-! # Verification correctness and ABI preservation against the shared contract -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem verifyStatus_u32 (result : Bool) :
    ((BitVec.ofNat 64 result.toNat).setWidth 32).toNat = if result then 1 else 0 := by
  cases result <;> rfl

theorem verifyingSharedPost {s t : State} (h : VerifyingABI s) (hp : VerifyingPost h.input s t) :
    (Spec.Dsa.verifyContract abi).post s t := by
  sig_post [Spec.Dsa.verifyContract, Spec.Dsa.verifySig, abi, argRegs, dsaVerifyStackArgs]
  sig_post [Spec.Dsa.verifyContract, Spec.Dsa.verifySig, abi, argRegs, dsaVerifyStackArgs]
  rw [hp.1, verifyStatus_u32]
  rfl

theorem verifyingCorrect (M : Mont)
    (s : State) (h : (Spec.Dsa.verifyContract abi).pre s) :
    ∃ trace t, Exec isa (SignVerify.verify M.mm) s trace t ∧ abiPreserved s t ∧
      (Spec.Dsa.verifyContract abi).post s t := by
  have ha := verifyingABI_of h
  obtain ⟨trace, t, he, hp⟩ := verifyingMain_ok M ha.pre
  exact ⟨trace, t, he, abiPreserved_of_keep hp.2.2, verifyingSharedPost ha hp⟩

end VG.Proof.Dsa.AArch64
