module

public import VerifiedGarbage.TCB.Arm.Isa

/-!
# Full-width products using ARMv7's constant-time multiply

RSA's variable-width arithmetic keeps packed words, rather than allocating
one word for every half digit. The product of two 32-bit words is assembled
from four 16-by-16 products using only `mul`; no long multiply instruction
or operand-dependent branch is needed. This preserves the ARMv7 model's
baseline, including cores with early-terminating long multiplication.
-/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG.Arm

/-- Split `r1` and `r2` into half words: `r3`, `r4` and `r5`, `r6`.
`r9` holds the mask `0xffff`. -/
def splitWords : List Instr :=
  [.movw .r9 0xffff,
    .dp .and .r3 .r1 (.reg .r9), .mov .r4 (.shifted .r1 .lsr 16),
    .dp .and .r5 .r2 (.reg .r9), .mov .r6 (.shifted .r2 .lsr 16)]

/-- Low product and the first cross product, including the low product's
carry. The addition fits in one word. -/
def lowProduct : List Instr :=
  [.mul .r7 .r3 .r5, .mul .r8 .r4 .r5,
    .dp .add .r8 .r8 (.shifted .r7 .lsr 16)]

/-- High product and the second cross product, including the low half of
the first cross product. Both additions fit in one word. -/
def crossProduct : List Instr :=
  [.dp .and .r5 .r8 (.reg .r9), .mul .r4 .r4 .r6,
    .dp .add .r4 .r4 (.shifted .r8 .lsr 16),
    .mul .r3 .r3 .r6, .dp .add .r3 .r3 (.reg .r5)]

/-- Finish the high word and assemble the low word. -/
def packProduct : List Instr :=
  [.dp .add .r4 .r4 (.shifted .r3 .lsr 16),
    .dp .and .r7 .r7 (.reg .r9),
    .dp .add .r3 .r7 (.shifted .r3 .lsl 16)]

/-- `r4:r3 = r1 * r2`, preserving all other registers except `r5`–`r9`.
No memory access, flag modification, stack use or branch. -/
def wideMul : List Instr := splitWords ++ lowProduct ++ crossProduct ++ packProduct

end VG.Impl.Bignum.Arm
