module

public import VerifiedGarbage.Impl.Rsa.Arm.PrivChecked
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Rsa.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Arm.CallF

/-! # Verified callees for the ARMv7 checked private operation

Each callee uses at most 56 stack bytes. Callers are generic over the CRT
and its associated public implementation, so future variants propagate.
-/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm

structure CrtImpl where
  name : String
  code : Prog isa
  verified : Verified target code (Proof.Rsa.privateCrtContract abi 56)
  stack : FrameStack.armStack code ≤ 56
  pcName : String
  pc : Prog isa
  pcVerified : Verified target pc (Spec.Rsa.publicPrecomputeContract abi 56)
  pcStack : FrameStack.armStack pc ≤ 56
  pdName : String
  pd : Prog isa
  pdVerified : Verified target pd (Spec.Rsa.publicPrecomputedCheckedContract abi 56)
  pdStack : FrameStack.armStack pd ≤ 56
  suffix : String
  features : List String

def privName (v : CrtImpl) : String := Spec.Rsa.privateCheckedApi.name ++ v.suffix
def privCode (v : CrtImpl) : Prog isa := Impl.Rsa.Arm.PrivChecked.code v.name v.code v.pcName v.pc v.pdName v.pd
/-- Inner frame, register save, and the largest callee frame. -/
def stackBytes : Nat := 3440
end VG.Proof.Rsa.Arm
