module

public import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingABIPost
public import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingAgreement
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Dsa.X86_64.EqualCT
import VerifiedGarbage.Proof.Dsa.X86_64.JointCallCT
import VerifiedGarbage.Proof.Dsa.X86_64.ReadyMinusCT
import VerifiedGarbage.Proof.Dsa.X86_64.ReadyRangeCT
import VerifiedGarbage.Proof.Dsa.X86_64.ZeroCT
import VerifiedGarbage.Proof.MdStream.Spec

/-! # DSA verifying verified against the shared contract -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Dsa.X86_64
open VG.Proof.Bignum.X86_64

/-- An ordinary 1024/160 call with disjoint buffers and an empty digest.
The all-zero key is allowed by the contract and is rejected by the program. -/
def verifyingSatState : State where
  gpr r := match r with
    | .rdi => 0x2000 | .rsi => 404 | .rdx => 128 | .rcx => 20
    | .r8 => 0x4000 | .r9 => 40 | .rsp => 0x10000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x10009 then 0x50 else if a = 0x10019 then 0x80
    else if a = 0x10021 then 8 else 0
  rd := [⟨0x2000, 404⟩, ⟨0x4000, 40⟩, ⟨0x5000, 0⟩, ⟨0x10008, 32⟩]
  wr := [⟨0x8000, 16384⟩]

theorem verifyingSatisfiable : ∃ s, (Spec.Dsa.verifyContract abi).pre s := by
  sig_implies_sat [Spec.Dsa.verifyContract, Spec.Dsa.verifySig, abi, argRegs, stackArgs_four]
    [verifyingSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using verifyingSatState

theorem verifying_verified (M : Mont)
    (hmx : (SignVerify.verify M.mm).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target (SignVerify.verify M.mm) (Spec.Dsa.verifyContract abi) :=
  ⟨verifyingCorrect M hmx, verifyingConstantTime M, verifyingSatisfiable⟩

end VG.Proof.Dsa.X86_64
