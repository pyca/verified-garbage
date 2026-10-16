module

public import VerifiedGarbage.Proof.Dsa.AArch64.SigningABIPost
import VerifiedGarbage.Proof.Dsa.AArch64.SigningAgreement
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Dsa.AArch64.EqualCT
import VerifiedGarbage.Proof.Dsa.AArch64.ReadyMinusCT
import VerifiedGarbage.Proof.Dsa.AArch64.ReadyRangeCT
import VerifiedGarbage.Proof.Dsa.AArch64.ZeroCT
import VerifiedGarbage.Proof.MdStream.Spec

/-! # DSA signing verified against the shared contract -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Dsa.AArch64
open VG.Proof.Bignum.AArch64

/-- An ordinary 1024/160 call with disjoint buffers and an empty digest.
The all-zero key is allowed by the contract and is rejected by the program. -/
def signingSatState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 40 | .x2 => 0x2000 | .x3 => 424
    | .x4 => 128 | .x5 => 0x4000 | .x6 => 20 | .x7 => 0x5000 | _ => 0
  sp := 0x10000
  mem a := if a = 0x10009 then 0x80 else if a = 0x10011 then 8 else 0
  rd := [⟨0x2000, 424⟩, ⟨0x4000, 20⟩, ⟨0x5000, 0⟩, ⟨0x10000, 24⟩]
  wr := [⟨0x1000, 40⟩, ⟨0x8000, 16384⟩]

theorem signingSatisfiable : ∃ s, (Spec.Dsa.signContract abi).pre s := by
  sig_implies_sat [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, dsaSignStackArgs]
    [signingSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using signingSatState

theorem signing_verified (M : Mont) :
    Verified target (SignVerify.sign M.mm) (Spec.Dsa.signContract abi) :=
  ⟨signingCorrect M, signingConstantTime M, signingSatisfiable⟩

end VG.Proof.Dsa.AArch64
