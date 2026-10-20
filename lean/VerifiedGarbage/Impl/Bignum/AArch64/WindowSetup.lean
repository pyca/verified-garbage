module
public import VerifiedGarbage.Impl.Bignum.AArch64.Core


/-! Load only the public pointers and width needed by the next window phase.
The zero register is retained across the arithmetic; reduction loads its own modulus. -/

@[expose] public section
namespace VG.Impl.Bignum.AArch64.WindowSetup
open VG VG.AArch64 VG.Impl.Bignum.AArch64

def start : List Instr :=
 [ldh .x8 (sArr Public.aAcc), .addImm .x .x8 .x8 16, ldh .x12 sW, movi .x7 0]
def square (a : Nat) : List Instr :=
 [ldh .x8 (sArr Public.aAcc), .addImm .x .x8 .x8 16, ldh .x9 (sArr a), ldh .x12 sW]
def product : List Instr :=
 [ldh .x8 (sArr Public.aAcc), .addImm .x .x8 .x8 16, ldh .x12 sW]

end VG.Impl.Bignum.AArch64.WindowSetup
