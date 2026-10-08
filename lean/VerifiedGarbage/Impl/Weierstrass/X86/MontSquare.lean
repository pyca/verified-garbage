import VerifiedGarbage.Impl.Weierstrass.X86.Mont
import VerifiedGarbage.Impl.X25519.X86

/-! # Full-width P-256 squaring for the x86 Montgomery callee -/
namespace VG.Impl.Weierstrass.X86.Mont
open VG.X86 VG.Impl.Mont.X86

/-- Sparse reduction of an already populated product. Unlike CIOS, carry
and borrow propagate through every remaining high word. -/
def squareRed (acc extra : Nat) : List Instr :=
  [.mov .eax (.imm 0), .store (bp acc) .eax] ++
  multiChain (acc + 12) positiveMask (7 + extra) ++
  sparseChain (acc + 28) .sub .sbb (3 + extra)

/-- One full-product REDC round, including its reduction digit. -/
def squareRound (i : Nat) : List Instr :=
  [.mov .ecx (.mem (bp (own 4 + 4 * i)))] ++ squareRed (own 4 + 4 * i) (7 - i)

/-- The first `r` reduction rounds. -/
def squareRounds : Nat → List Instr
  | 0 => []
  | r + 1 => squareRounds r ++ squareRound r

/-- Copy the operand through `esi` into the temporary words before Comba
uses the general-purpose registers for its accumulator. -/
def squareCopy : Nat → List Instr
  | 0 => []
  | j + 1 => squareCopy j ++
    [.mov .eax (.mem (at_ .esi (4 * j))), .store (bp (tmpAt 4 + 4 * j)) .eax]

/-- The sixteen Comba columns, before modular reduction. -/
def squareProduct : List Instr :=
  VG.Impl.X25519.X86.zeroAcc ++
    VG.Impl.X25519.X86.cols (own 4) 16 (VG.Impl.X25519.X86.sqrTerms (tmpAt 4))

/-- Restore the Montgomery base after the Comba accumulator used `ebp`. -/
def squareProductBase : List Instr := squareProduct ++ [.mov .ebp (.reg .edi)]

/-- Copy, square, and initialize the extra high word for REDC. -/
def squareInit : List Instr :=
  squareCopy 8 ++ [.mov .edi (.reg .ebp)] ++ squareProductBase ++
    [.store (bp (own 4 + 64)) .ebx]

/-- The square before the common final conditional subtraction. -/
def squareBody : List Instr := squareInit ++ squareRounds 8

end VG.Impl.Weierstrass.X86.Mont
