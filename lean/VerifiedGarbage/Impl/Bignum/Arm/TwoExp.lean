module

public import VerifiedGarbage.Impl.Bignum.Arm.DoubleFnBody
public import VerifiedGarbage.Impl.Bignum.Arm.Exp
public import VerifiedGarbage.Impl.Bignum.Arm.SelectArray

/-! # Constant-time binary exponentiation for the public generator two

The arithmetic actions are supplied by the caller, so this loop can call
shared Montgomery routines instead of embedding another copy of them.
Array 5 holds ordinary two, array 6 the running Montgomery power, and
array 1 the doubled candidate. Every bit squares, doubles, and selects.
-/

@[expose] public section

namespace VG.Impl.Bignum.Arm.TwoExp
open VG VG.Arm

/-- Extract a secret bit into the branchless array selector's bit register. -/
def digit : List Instr :=
  [.ldr .r11 .r0 200, .mov .r11 (.shifted .r11 .lsr 7), .dp .and .r11 .r11 (.imm 1)]

def bit (square twice : Prog isa) : Prog isa :=
  .seq square (.seq twice (.seq (.block digit) (selectArray 6 6 1)))

def round (square twice : Prog isa) : Prog isa :=
  .seq (bit square twice) (.seq (.block expShift) (.block expDecrement))

def bits (square twice : Prog isa) : Prog isa := .loop (round square twice) .ne

def bytes (square twice : Prog isa) : Prog isa :=
  .loop (.seq expByteHead (.seq (bits square twice) (.block expByteNext))) .ne

/-- A linear modular doubling into the branchless selector's candidate array. -/
def candidate : Prog isa := .seq (.block (montOpArgs 1 5 6)) doubleFnRestore

/-- Form Montgomery one and retain ordinary two for the linear candidate. -/
def initial (multiply : Prog isa) : Prog isa :=
  .seq (smallConst 7 1) (.seq multiply (smallConst 5 2))

/-- Initialize, process the entire supplied scalar, and decode the result. -/
def phase (initial square twice finish : Prog isa) : Prog isa :=
  .seq initial (.seq (bytes square twice) finish)

end VG.Impl.Bignum.Arm.TwoExp
