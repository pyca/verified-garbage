module

public import VerifiedGarbage.TCB.Arm.Isa

/-! # A masked-add row for ARMv7: `[o] += m & [b]`, with no multiply

`maskRow` adds the `n` words at `r12`, ANDed with the mask `r1` (`0` or all ones), and the carry
`r11` into the `n` words at `r0`, with `row`'s registers: the carry out in `r11`, and both
pointers past their words. It is `row` for a scalar of `0` or `1`, without the products. -/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG.Arm

/-- A word: `[r0] += (r1 & [r12]) + r11`, the carry out in `r11`, through `r2`–`r4` and `r10 = 0`;
then the pointers forward and the count in `lr` down, which sets the loop's condition. -/
def maskWord : List Instr :=
  [.ldr .r2 .r12 0, .ldr .r3 .r0 0, .dp .and .r2 .r2 (.reg .r1),
   .adds .r3 .r3 (.reg .r2), .adc .r4 .r10 (.imm 0),
   .adds .r3 .r3 (.reg .r11), .adc .r11 .r4 (.imm 0), .str .r3 .r0 0,
   .dp .add .r0 .r0 (.imm 4), .dp .add .r12 .r12 (.imm 4), .subs .lr .lr (.imm 1)]

/-- `lr > 0` words of `[r0] += r1 & [r12]`, plus the carry `r11`. -/
def maskRow : Prog isa := .seq (.block [.mov .r10 (.imm 0)]) (.loop (.block maskWord) .ne)

end VG.Impl.Bignum.Arm
