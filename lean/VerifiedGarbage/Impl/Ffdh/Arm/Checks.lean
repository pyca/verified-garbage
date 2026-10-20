module

import VerifiedGarbage.Impl.Ffdh.Arm.Arithmetic
public import VerifiedGarbage.Impl.Bignum.Arm.SelectArray
public import VerifiedGarbage.Impl.Bignum.Arm.ArrayCompare
public import VerifiedGarbage.Impl.Bignum.Arm.R2

/-! Fixed-width FFDH comparisons using RSA's native subtraction and selection.
The flag is r11. Header offset 136 holds the saved flag across arithmetic. -/

@[expose] public section
namespace VG.Impl.Ffdh.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

/-- Copy an array, including when the source equals the destination. -/
def copy (o a : Nat) : Prog isa :=
  .seq (.block [.mov .r11 (.imm 0)]) (selectArray o a a)

def saveFlag : List Instr := [.str .r11 .r0 136]
def andFlag : List Instr := [.ldr .r3 .r0 136, .dp .and .r11 .r11 (.reg .r3)]

/-- Equality computed from both unsigned comparisons. -/
def equal (a b : Nat) : Prog isa := .seq (arrayCompare a b)
  (.seq (.block saveFlag) (.seq (arrayCompare b a)
    (.block [.ldr .r3 .r0 136, .dp .orr .r11 .r11 (.reg .r3), .dp .eor .r11 .r11 (.imm 1)])))

def isOne (a : Nat) : Prog isa := .seq (smallConst 7 1) (equal a 7)
def greaterOne (a : Nat) : Prog isa := .seq (smallConst 7 1) (arrayCompare 7 a)
def nonzero (a : Nat) : Prog isa := .seq (smallConst 7 1)
  (.seq (arrayCompare a 7) (.block [.dp .eor .r11 .r11 (.imm 1)]))

def setLowBit : List Instr := [
  .ldr .r4 .r0 120, .ldr .r3 .r4 0, .dp .orr .r3 .r3 (.imm 1), .str .r3 .r4 0]

/-- For odd p, x < p-1 iff x|1 < p. Array 7 is temporary; RSA's
exponentiation initializes it back to one before Montgomery operations. -/
def belowP (a : Nat) : Prog isa := .seq (copy 7 a)
  (.seq (.block setLowBit)
    (arrayCompare 7 0))

def inRange (a : Nat) : Prog isa := .seq (greaterOne a)
  (.seq (.block saveFlag) (.seq (belowP a) (.block andFlag)))

def odd (a : Nat) : Prog isa := .block [
  .ldr .r4 .r0 (64 + 8 * a), .ldrb .r11 .r4 0, .dp .and .r11 .r11 (.imm 1)]

end VG.Impl.Ffdh.Arm
