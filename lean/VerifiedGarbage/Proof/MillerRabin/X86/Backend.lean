module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.MillerRabin.Contract
public import VerifiedGarbage.TCB.X86.Target

/-! # Prepared i686 Miller–Rabin implementations for generic callers -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86

structure RoundImpl where
  code : Prog isa
  verified : Verified target code (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96)
  noSp : NoSp code
  spSafe : code.allInstrs (fun i => !isa.writesSp i) = true
  stack : stackUse code ≤ 96
  suffix : String
  features : List String

def RoundImpl.name (v : RoundImpl) : String :=
  "vg_miller_rabin_round" ++ v.suffix

end VG.Proof.MillerRabin.X86
