module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Spec.MillerRabin
public import VerifiedGarbage.TCB.X86.Target

/-! # Prepared i686 Miller–Rabin implementations for generic callers -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86

structure RoundImpl where
  code : Prog isa
  verified : Verified target code (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact 56)
  noSp : NoSp code
  spSafe : code.allInstrs (fun i => !isa.writesSp i) = true
  stack : stackUse code ≤ 56
  suffix : String
  features : List String

def RoundImpl.name (v : RoundImpl) : String :=
  (Spec.MillerRabin.roundApi Spec.MillerRabin.compact).name ++ v.suffix

end VG.Proof.MillerRabin.X86
