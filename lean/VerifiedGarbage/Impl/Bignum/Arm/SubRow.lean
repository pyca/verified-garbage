module

public import VerifiedGarbage.Impl.Bignum.Arm.Sub
public import VerifiedGarbage.Impl.Bignum.Arm.Row

/-! # Runtime-length subtraction for final Montgomery reduction -/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def subStep : Prog isa :=
  .seq (.block [.ldr .r1 .r10 0, .ldr .r2 .r12 0])
    (.seq (.block subBorrow) (.block [.str .r3 .r0 0]))

def subAdvance : List Instr := .dp .add .r10 .r10 (.imm 4) :: rowAdvance

def subBody : Prog isa := .seq subStep (.block subAdvance)

/-- Subtract `lr` words at `r12` from those at `r10`, with incoming borrow
`r11`, writing to `r0`. The nonzero count and pointers are public. -/
def subRow : Prog isa := .loop subBody .ne

end VG.Impl.Bignum.Arm
