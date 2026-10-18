module

public import VerifiedGarbage.Impl.Bignum.Arm.RowStep

/-! # Runtime-length packed-word rows for ARMv7 RSA -/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

/-- Advance the two pointers and decrement the public word count in `lr`.
The final subtraction supplies the loop condition. -/
def rowAdvance : List Instr :=
  [.dp .add .r0 .r0 (.imm 4), .dp .add .r12 .r12 (.imm 4), .subs .lr .lr (.imm 1)]

def rowBody : Prog isa := .seq rowStep (.block rowAdvance)

/-- Split the scalar `r1` once for the row: its low half in `r1`, its high
half in `r10`, and the mask `0xffff` in `r9`. -/
def rowSplit : List Instr :=
  [.movw .r9 0xffff, .mov .r10 (.shifted .r1 .lsr 16), .dp .and .r1 .r1 (.reg .r9)]

/-- Put the scalar back together in `r1`. -/
def rowJoin : List Instr := [.dp .orr .r1 .r1 (.shifted .r10 .lsl 16)]

def rowLoop : Prog isa := .loop rowBody .ne

/-- Add `r1` times `lr` input words at `r12`, plus carry `r11`, into the
same number of accumulator words at `r0`. `lr` must initially be nonzero.
The carry out remains in `r11`; both pointers finish past their arrays, and
`r1` is the scalar again. -/
def row : Prog isa := .seq (.block rowSplit) (.seq rowLoop (.block rowJoin))

end VG.Impl.Bignum.Arm
