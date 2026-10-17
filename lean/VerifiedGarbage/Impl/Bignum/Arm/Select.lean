module

public import VerifiedGarbage.Impl.Bignum.Arm.SubRow

/-! # Branch-free selection for the final modular reduction -/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

/-- Select `r1` for bit zero or `r2` for bit one, putting the result in
`r3`. The bit in `r11` and the flags are preserved. -/
def selectWord : List Instr :=
  [.mov .r4 (.imm 0), .dp .sub .r4 .r4 (.reg .r11),
   .dp .eor .r3 .r1 (.reg .r2), .dp .and .r3 .r3 (.reg .r4),
   .dp .eor .r3 .r3 (.reg .r1)]

def selectStep : Prog isa :=
  .seq (.block [.ldr .r1 .r10 0, .ldr .r2 .r12 0])
    (.seq (.block selectWord) (.block [.str .r3 .r0 0]))

def selectBody : Prog isa := .seq selectStep (.block subAdvance)

/-- Select `lr` words from `r10` or `r12` using the secret bit `r11`,
writing to `r0`. The count is nonzero. -/
def selectRow : Prog isa := .loop selectBody .ne

end VG.Impl.Bignum.Arm
