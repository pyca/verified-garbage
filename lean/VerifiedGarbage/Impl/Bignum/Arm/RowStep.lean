module

public import VerifiedGarbage.Impl.Bignum.Arm.Mac

/-! # One packed-word row step for ARMv7 Montgomery arithmetic

The row's scalar `x` stays split into its 16-bit halves for the whole row
(`row`'s prologue): `r1 = x & 0xffff`, `r10 = x >> 16`, and the mask
`0xffff` in `r9`. Each step then splits only the input word, forms the four
16 × 16-bit products of `x` and the word, and adds the two cross products,
which have weight `2¹⁶`, into the low and high product words with `adds` and
`adc` on shifted operands, so that every carry is taken by the instruction
after the one that makes it. -/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG.Arm

/-- The input word's halves: `r2 = r2 & 0xffff`, `r6 = r2 >> 16`. -/
def rowHalves : List Instr := [.mov .r6 (.shifted .r2 .lsr 16), .dp .and .r2 .r2 (.reg .r9)]

/-- The four partial products, with the scalar's halves in `r1` and `r10`
and the input word's in `r2` and `r6`: `r3 = x₀ y₀`, `r4 = x₁ y₁`, and the
cross products `r5 = x₁ y₀` and `r7 = x₀ y₁`. -/
def rowPartials : List Instr :=
  [.mul .r3 .r1 .r2, .mul .r5 .r10 .r2, .mul .r7 .r1 .r6, .mul .r4 .r10 .r6]

/-- `r4:r3 += 2¹⁶ r`: the cross product's low half into the low word, with
its carry and its high half into the high word. -/
def addCross (r : Reg) : List Instr :=
  [.adds .r3 .r3 (.shifted r .lsl 16), .adc .r4 .r4 (.shifted r .lsr 16)]

/-- `r4:r3 = x * r2`, from the input word's halves and the four partial
products. -/
def rowProduct : List Instr := rowHalves ++ rowPartials ++ addCross .r5 ++ addCross .r7

/-- `r11:r3 := r4:r3 + r11`: the carry added in, and the high word, with its
carry, the next carry. -/
def addCarry : List Instr := [.adds .r3 .r3 (.reg .r11), .adc .r11 .r4 (.imm 0)]

/-- Add `x * [r12 + k] + r11` into `[r0 + k]`, retaining the high word in
`r11`. The row's pointers and the scalar's halves survive. The enclosing
loop advances the pointers and handles its public counter separately. -/
def rowStepAt (k : Nat) : Prog isa :=
  .seq (.block [.ldr .r2 .r12 k]) (.seq (.block rowProduct)
    (.seq (.block [.ldr .r5 .r0 k])
      (.seq (.block (addWord .r5 ++ addCarry)) (.block [.str .r3 .r0 k]))))

/-- The step at the pointers themselves. -/
def rowStep : Prog isa := rowStepAt 0

end VG.Impl.Bignum.Arm
