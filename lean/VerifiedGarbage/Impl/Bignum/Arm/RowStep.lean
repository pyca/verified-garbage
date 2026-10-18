module

public import VerifiedGarbage.Impl.Bignum.Arm.Mac

/-! # One packed-word row step for ARMv7 Montgomery arithmetic

The row's scalar `x` stays split into its 16-bit halves for the whole row
(`row`'s prologue): `r1 = x & 0xffff`, `r10 = x >> 16`, and the mask
`0xffff` in `r9`. Each step then splits only the input word, and forms
`x * [r12]` from the same four 16 × 16-bit products as `wideMul`. -/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

/-- The input word's halves: `r2 = r2 & 0xffff`, `r6 = r2 >> 16`. -/
def rowHalves : List Instr := [.mov .r6 (.shifted .r2 .lsr 16), .dp .and .r2 .r2 (.reg .r9)]

/-- `wideMul`'s low product and first cross product (`lowProduct`), with
the scalar's halves in `r1` and `r10`. -/
def rowLow : List Instr :=
  [.mul .r7 .r1 .r2, .mul .r8 .r10 .r2, .dp .add .r8 .r8 (.shifted .r7 .lsr 16)]

/-- The high product and second cross product (`crossProduct`), the latter
accumulated by one `mla`. -/
def rowCross : List Instr :=
  [.dp .and .r5 .r8 (.reg .r9), .mul .r4 .r10 .r6, .dp .add .r4 .r4 (.shifted .r8 .lsr 16),
   .mla .r3 .r1 .r6 .r5]

/-- `r4:r3 = x * r2`, from the input word's halves and `wideMul`'s partial
products. -/
def rowProduct : List Instr := rowHalves ++ rowLow ++ rowCross ++ packProduct

/-- Add `x * [r12] + r11` into `[r0]`, retaining the high word in `r11`.
The row's pointers and the scalar's halves survive. The enclosing loop
advances the pointers and handles its public counter separately. -/
def rowStep : Prog isa :=
  .seq (.block [.ldr .r2 .r12 0]) (.seq (.block rowProduct)
    (.seq (.block [.ldr .r5 .r0 0])
      (.seq (.block (addWord .r5 ++ addWord .r11)) (.block [.str .r3 .r0 0, .mov .r11 (.reg .r4)]))))

end VG.Impl.Bignum.Arm
