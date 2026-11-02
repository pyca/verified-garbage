module

public import VerifiedGarbage.Impl.Rsa.X86.PrivChecked
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Rsa.Contract
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.Contract

/-! # Verified callees and stack bounds for checked private RSA -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86

structure CrtImpl where
  name : String
  code : Prog isa
  verified : Verified target code (Proof.Rsa.privateCrtContract abi 96)
  stack : stackUse code ≤ 96
  noSp : NoSp code
  pcName : String
  pc : Prog isa
  pcVerified : Verified target pc (Spec.Rsa.publicPrecomputeContract abi 96)
  pcStack : stackUse pc ≤ 96
  pcNoSp : NoSp pc
  pdName : String
  pd : Prog isa
  pdVerified : Verified target pd (Spec.Rsa.publicPrecomputedCheckedContract abi 96)
  pdStack : stackUse pd ≤ 96
  pdNoSp : NoSp pd
  suffix : String := ""
  features : List String := []

def privCode (v : CrtImpl) : Prog isa :=
  Impl.Rsa.X86.PrivChecked.code v.name v.code v.pcName v.pc v.pdName v.pd

/-- Local frame, saved registers, and the largest callee plus its return address. -/
def stackBytes : Nat := 3444

end VG.Proof.Rsa.X86.PrivChecked
