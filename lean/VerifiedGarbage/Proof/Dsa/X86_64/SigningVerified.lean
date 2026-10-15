module

public import VerifiedGarbage.Proof.Bignum.X86_64.MontSq
public import VerifiedGarbage.Proof.Dsa.X86_64.SigningABIPost
import VerifiedGarbage.Proof.Dsa.X86_64.SigningAgreement
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

/-! # DSA signing verified against the shared contract -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Dsa.X86_64
open VG.Proof.Bignum.X86_64

/-- An ordinary 1024/160 call with disjoint buffers and an empty digest.
The all-zero key is allowed by the contract and is rejected by the program. -/
def signingSatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 40 | .rdx => 0x2000 | .rcx => 424
    | .r8 => 128 | .r9 => 0x4000 | .rsp => 0x10000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x10008 then 20 else if a = 0x10011 then 0x50
    else if a = 0x10021 then 0x80 else if a = 0x10029 then 8 else 0
  rd := [⟨0x2000, 424⟩, ⟨0x4000, 20⟩, ⟨0x5000, 0⟩, ⟨0x10008, 40⟩]
  wr := [⟨0x1000, 40⟩, ⟨0x8000, 16384⟩]

theorem signingSatisfiable : ∃ s, (Spec.Dsa.signContract abi).pre s := by
  sig_implies_sat [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, stackArgs_five]
    [signingSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using signingSatState

theorem signing_verified (M : Mont) (Sq : MontS)
    (hmx : (SignVerify.sign Sq.mm M.mm).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target (SignVerify.sign Sq.mm M.mm) (Spec.Dsa.signContract abi) :=
  ⟨signingCorrect M Sq hmx, signingConstantTime M Sq, signingSatisfiable⟩

end VG.Proof.Dsa.X86_64
