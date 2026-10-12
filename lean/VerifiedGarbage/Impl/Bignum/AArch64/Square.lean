module

public import VerifiedGarbage.Impl.Bignum.AArch64.Core

/-!
# AArch64 Montgomery squaring

The full product occupies the existing adjacent accumulator and temporary arrays,
starting two words into the accumulator. Each cross-product is computed
once, then doubled with diagonal squares added before Montgomery reduction.
Four-word MAC blocks keep the existing deferred-carry arithmetic and retain
scalar tails. Array indices are fixed when the program is constructed;
loops and the small-size fallback depend only on the public limb count.
-/

@[expose] public section

namespace VG.Impl.Bignum.AArch64.Square
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64

def squareSetup (a : Nat) : List Instr :=
  [ldh .x8 (sArr Public.aAcc), .addImm .x .x8 .x8 16,
   ldh .x9 (sArr a), ldh .x10 (sArr Public.aN), ldh .x12 sW,
   ldh .x15 sMinv, movi .x7 0]

def zeroWide : Prog isa :=
  .seq (.block [mov .x16 .x8, .add .x .x14 .x12 .x12, .addImm .x .x14 .x14 2])
    (countLoop .x14 [st .x7 .x16, next .x16])

def diagonalHead : List Instr :=
  [ld .x1 .x11, .mul .x .x2 .x1 .x1, .umulh .x1 .x1 .x1,
   ld .x3 .x16, ld .x4 .x16 8]

def diagonalCore : List Instr :=
  [.adds .x .x3 .x3 .x3, .adcs .x .x4 .x4 .x4, .adc .x .x6 .x7 .x7,
   .adds .x .x3 .x3 .x2, .adcs .x .x4 .x4 .x1, .adc .x .x6 .x6 .x7,
   .adds .x .x3 .x3 .x5, .adcs .x .x4 .x4 .x7, .adc .x .x5 .x6 .x7]

def diagonalTail : List Instr :=
  [st .x3 .x16, st .x4 .x16 8, .addImm .x .x16 .x16 16, next .x11]

def diagonalStep : List Instr := diagonalHead ++ diagonalCore ++ diagonalTail

def diagonal : Prog isa :=
  .seq (.block [mov .x16 .x8, mov .x11 .x9, mov .x14 .x12, movi .x5 0])
    (.seq (countLoop .x14 diagonalStep) (.block [st .x5 .x16]))

/-- Four consecutive deferred-carry MACs; pointer increments once per block. -/
def macAt (k : Nat) : List Instr :=
  [ld .x3 .x17 (8*k), .mul .x .x4 .x1 .x3, .umulh .x3 .x1 .x3,
   .adcs .x .x4 .x4 .x2, .adc .x .x2 .x3 .x7,
   ld .x3 .x16 (8*k), .adds .x .x4 .x4 .x3, st .x4 .x16 (8*k)]

def mac4 : List Instr := (List.range 4).flatMap macAt ++
  [ .addImm .x .x16 .x16 32, .addImm .x .x17 .x17 32 ]

def tiledRow (count : Reg) : Prog isa :=
  .seq (.block [.lsr .x .x14 count 2])
    (.seq (.ite (.nonzero .x .x14) (countLoop .x14 mac4) (.block []))
      (.seq (.block [movi .x3 3, .logic .and .x .x14 count .x3])
        (.ite (.nonzero .x .x14) (countLoop .x14 (mac false)) (.block []))))

def crossRow : Prog isa :=
  .seq (.block [ld .x1 .x11, mov .x16 .x5, mov .x17 .x9,
      .adds .x .x2 .x7 .x7])
    (.seq (tiledRow .x13)
      (.block (carryOut ++ [st .x2 .x16, next .x5, next .x11,
        .addImm .x .x13 .x13 1, .subImm .x .x6 .x6 1])))

def cross : Prog isa :=
  .seq zeroWide (.seq (.block [.addImm .x .x5 .x8 8,
      .addImm .x .x11 .x9 8, movi .x13 1, .subImm .x .x6 .x12 1])
    (.loop crossRow (.nonzero .x .x6)))

def redcHead : List Instr :=
  [ld .x3 .x8, .mul .x .x1 .x3 .x15, mov .x16 .x8,
   mov .x17 .x10, .adds .x .x2 .x7 .x7]

def redcTail : List Instr :=
  [ld .x3 .x16, .adds .x .x3 .x3 .x2, .adc .x .x6 .x7 .x7,
   .adds .x .x3 .x3 .x5, .adc .x .x5 .x6 .x7,
   st .x3 .x16, next .x8, .subImm .x .x13 .x13 1]

def redcRow : Prog isa :=
  .seq (.block redcHead) (.seq (tiledRow .x12)
    (.seq (.block carryOut) (.block redcTail)))

def redc : Prog isa :=
  .seq (.block [mov .x13 .x12, movi .x5 0])
    (.seq (.loop redcRow (.nonzero .x .x13))
      (.block [next .x16, st .x5 .x16, st .x7 .x16 8]))

def rawSquare (a : Nat) : Prog isa :=
  .seq (.block (squareSetup a)) (.seq cross diagonal)

def finishBases (o : Nat) : List Instr := [ldh .x5 (sArr o), ldh .x6 (sArr Public.aAcc)]

def square (o a : Nat) : Prog isa :=
  .seq (rawSquare a) (.seq redc
    (.seq (.block (finishBases o))
      (.seq subMod selectAcc)))

def guard : List Instr := [ldh .x12 sW, .lsr .x .x3 .x12 3]

/-- Public limb-count guard retains the existing kernel below eight words. -/
def montMul (o a b : Nat) : Prog isa :=
  if a = b then
    .seq (.block guard)
      (.ite (.nonzero .x .x3) (square o a) (Public.basicMm o a b))
  else Public.basicMm o a b

end VG.Impl.Bignum.AArch64.Square
