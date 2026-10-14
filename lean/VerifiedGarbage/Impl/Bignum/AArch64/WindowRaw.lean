module

public import VerifiedGarbage.Impl.Bignum.AArch64.SquareEightRaw

/-! Arithmetic phases for a shared private-exponentiation window. The enclosing
window preserves the callee-saved registers once, across all six operations. -/

@[expose] public section
namespace VG.Impl.Bignum.AArch64.WindowRaw
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64

def triangle (a : Nat) : Prog isa :=
 .seq (.block (Square.squareSetup a))
 (.seq WideLoops.zero
 (.seq (.block [ldh .x8 (sArr a), .lsr .x .x12 .x12 3])
 (.seq (SquareEightRaw.rows a) (.block (Square.squareSetup a)))))

def square (a : Nat) : Prog isa := .seq (triangle a) WideLoops.diagonal

def product (a b : Nat) : Prog isa :=
 .seq (.block (Square.squareSetup a))
 (.seq WideLoops.zero
 (.seq (.block [ldh .x8 (sArr a), .lsr .x .x12 .x12 3])
 (.seq (ProductEight.rows a b) (.block (Square.squareSetup a)))))

end VG.Impl.Bignum.AArch64.WindowRaw
