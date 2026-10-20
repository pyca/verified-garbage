module

public import VerifiedGarbage.Impl.Bignum.AArch64.WindowSparse
public import VerifiedGarbage.Impl.Bignum.AArch64.WindowSetup

/-! Arithmetic phases for a shared private-exponentiation window. The enclosing
window preserves the callee-saved registers once, across all six operations. -/

@[expose] public section
namespace VG.Impl.Bignum.AArch64.WindowRaw
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64

def triangle (a : Nat) : Prog isa :=
 .seq (.block WindowSetup.start)
 (.seq (.block WindowSparse.padding)
 (.seq (.block [ldh .x8 (sArr a), .lsr .x .x12 .x12 3])
 (.seq (WindowSparse.rows a) (.block (WindowSetup.square a)))))

def square (a : Nat) : Prog isa := .seq (triangle a) WideLoops.diagonal

def product (a b : Nat) : Prog isa :=
 .seq (.block WindowSetup.start)
 (.seq WideLoops.zero
 (.seq (.block [ldh .x8 (sArr a), .lsr .x .x12 .x12 3])
 (.seq (ProductEight.rows a b) (.block WindowSetup.product))))

end VG.Impl.Bignum.AArch64.WindowRaw
