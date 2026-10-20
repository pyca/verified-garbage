module

public import VerifiedGarbage.Impl.Rsa.X86.PrivChecked
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.Contract

/-! # Verified callees and stack bounds for checked private RSA -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86

structure CrtImpl where
  name : String
  code : Prog isa
  verified : Verified target code (Spec.Rsa.privateCrtContract abi 40)
  stack : stackUse code ≤ 40
  noSp : NoSp code
  pcName : String
  pc : Prog isa
  pcVerified : Verified target pc (Spec.Rsa.publicPrecomputeContract abi 20)
  pcStack : stackUse pc ≤ 20
  pcNoSp : NoSp pc
  pdName : String
  pd : Prog isa
  pdVerified : Verified target pd (Spec.Rsa.publicPrecomputedCheckedContract abi 40)
  pdStack : stackUse pd ≤ 40
  pdNoSp : NoSp pd
  suffix : String := ""
  features : List String := []

def privCode (v : CrtImpl) : Prog isa :=
  Impl.Rsa.X86.PrivChecked.code v.name v.code v.pcName v.pc v.pdName v.pd

/-- Local frame, saved registers, and the largest callee plus its return address. -/
def stackBytes : Nat := 3388

end VG.Proof.Rsa.X86.PrivChecked
