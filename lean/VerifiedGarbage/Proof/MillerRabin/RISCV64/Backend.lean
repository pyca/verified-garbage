module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.MillerRabin.Contract
public import VerifiedGarbage.TCB.RISCV64.Target

-- separate module: the generic callers (RSA key generation, FFDH, DSA) import the interface without the round's proofs

/-! # Prepared RISC-V Miller–Rabin implementations for generic callers

A caller reaches the shared round by a call, from its `Verified` proof
(`WP.callAny`); the round's frames use at most 96 bytes of stack below the
stack pointer (`stack`), which the caller's own stack must cover, and it
calls nothing indirectly (`icalls`), which a caller's cleanup needs of the
code it runs (`RISCV64.Scrub.Fill`). -/

@[expose] public section
namespace VG.Proof.MillerRabin.RISCV64
open VG VG.RISCV64

structure RoundImpl where
  code : Prog isa
  verified : Verified target code (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96)
  stack : sdepth code ≤ 96
  icalls : RISCV64.Scrub.inames code = []
  suffix : String
  features : List String

def RoundImpl.name (v : RoundImpl) : String :=
  "vg_miller_rabin_round" ++ v.suffix

end VG.Proof.MillerRabin.RISCV64
