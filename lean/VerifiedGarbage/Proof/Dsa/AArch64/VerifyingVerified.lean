module
public import VerifiedGarbage.Impl.Dsa.AArch64.SignVerify
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Proof.Dsa.AArch64.Run
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Dsa.SignVerify

import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingABIPost
import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingAgreement

/-! # DSA verifying verified against the shared contract -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Dsa.AArch64
open VG.Proof.Bignum.AArch64

/-- An ordinary 1024/160 call with disjoint buffers and an empty digest.
The all-zero key is allowed by the contract and is rejected by the program. -/
def verifyingSatState : State where
  gpr r := match r with
    | .x0 => 0x2000 | .x1 => 404 | .x2 => 128 | .x3 => 20
    | .x4 => 0x4000 | .x5 => 40 | .x6 => 0x5000 | _ => 0
  sp := 0x10000
  mem a := if a = 0x10001 then 0x80 else if a = 0x10009 then 8 else 0
  rd := [⟨0x2000, 404⟩, ⟨0x4000, 40⟩, ⟨0x5000, 0⟩, ⟨0x10000, 16⟩]
  wr := [⟨0x8000, 16384⟩]

theorem verifyingSatisfiable : ∃ s, (Spec.Dsa.verifyContract abi).pre s := by
  sig_implies_sat [Spec.Dsa.verifyContract, Spec.Dsa.verifySig, abi, argRegs, dsaVerifyStackArgs]
    [verifyingSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using verifyingSatState

theorem verifying_verified (M : Mont) :
    Verified target (SignVerify.verify M.mm) (Spec.Dsa.verifyContract abi) :=
  ⟨verifyingCorrect M, verifyingConstantTime M, verifyingSatisfiable⟩

end VG.Proof.Dsa.AArch64
