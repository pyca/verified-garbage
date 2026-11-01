module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.PPC64LE.CallAny
public import VerifiedGarbage.Proof.MillerRabin.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target

/-! # Prepared PPC64LE Miller–Rabin implementations for generic callers

A caller reaches the shared round by a call, from its `Verified` proof
(`WP.callAny`); the round's frames use at most 176 bytes of stack below the
stack pointer (`stack`), which the caller's own stack must cover. -/

@[expose] public section
namespace VG.Proof.MillerRabin.PPC64LE
open VG VG.PPC64LE

structure RoundImpl where
  code : Prog isa
  verified : Verified target code (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 176)
  stack : sdepth code ≤ 176
  suffix : String
  features : List String

def RoundImpl.name (v : RoundImpl) : String :=
  "vg_miller_rabin_round" ++ v.suffix

end VG.Proof.MillerRabin.PPC64LE
