module

public import VerifiedGarbage.Impl.Bignum.Arm.RowFull
public import VerifiedGarbage.Impl.Bignum.Arm.HeaderControl

/-! # Full-width multiplication for CRT validation and recombination

The header holds the current scalar pointer (128), multiplicand pointer
(132), current output row (136), remaining rows (140), and words per row
(144). The output is zeroed before entering the nonempty loop.
-/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def wideProductArgsHead : List Instr := [.ldr .r12 .r0 132, .ldr .lr .r0 144, .ldr .r1 .r0 128]
def wideProductArgsTail : List Instr := [.ldr .r1 .r1 0, .mov .r11 (.imm 0), .ldr .r0 .r0 136]
def wideProductArgs : List Instr := wideProductArgsHead ++ wideProductArgsTail
def wideProductNext : Prog isa :=
  .seq (.block (headerIncrement 128 4))
    (.seq (.block (headerIncrement 136 4)) (.block (headerDecrement 140)))
def wideProductRow : Prog isa :=
  .seq (.block wideProductArgs) (.seq rowFull (.block [.ldrSp .r0 0]))
def wideProductBody : Prog isa := .seq wideProductRow wideProductNext
def wideProduct : Prog isa := .loop wideProductBody .ne

end VG.Impl.Bignum.Arm
