module

public import VerifiedGarbage.Impl.Bignum.Arm.Row
public import VerifiedGarbage.Impl.Subst

/-! # Rows with `umaal` for ARMv7 Montgomery arithmetic

`rowU` adds `r1` times the input words at `r12` into the accumulator words
at `r0`, as `row` does, with one `umaal` a word (`hi:lo := n * m + hi + lo`)
for the 16-bit products and carries `row` uses: the scalar is joined into
`r9` for the loop over pairs of words, and `r11` carries. After the loop,
`rowUEnd` leaves every register as `row` does after its last step (the
input word's halves in `r2` and `r6`, `r7 = x₀ y₁`, the accumulator word
in `r5`, the high word of `x y + a` in `r4`, the mask in `r9`), so that
`rowU` ends in the state `row` ends in: its proofs are `row`'s
(`Proof/Bignum/Arm/RowUmaal.lean`). It needs the CPU feature `umaal`. -/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG.Arm

/-- Add `r9 * [r12 + k] + r11` into `[r0 + k]`, the high word into `r11`,
leaving the input word in `r2` and the accumulator's in `r5`. -/
def rowStepU (k : Nat) : List Instr :=
  [.ldr .r2 .r12 k, .ldr .r3 .r0 k, .mov .r5 (.reg .r3), .umaal .r3 .r11 .r2 .r9, .str .r3 .r0 k]

/-- The first word of a pair does not need its old accumulator in `r5`. -/
def rowFirstU : List Instr :=
  [.ldr .r2 .r12 0, .ldr .r3 .r0 0, .umaal .r3 .r11 .r2 .r9, .str .r3 .r0 0]

/-- Two steps, at the pointers and a word above them, then the advance.
Only the second accumulator word is needed by `rowUEnd`. -/
def rowBodyU : List Instr := rowFirstU ++ rowStepU 4 ++ rowAdvance2

/-- The scalar `r1 | r10 << 16` into `r9`. -/
def rowUJoin : List Instr := [.dp .orr .r9 .r1 (.shifted .r10 .lsl 16)]

/-- The registers `row`'s last step leaves, from the input word `y` in
`r2`, the accumulator word `a` in `r5` and the scalar `x` in `r9`:
`r4 = (x y + a) >> 32`, `r6 = y >> 16`, `r2 = y & 0xffff`, `r9 = 0xffff`
and `r7 = (x & 0xffff) (y >> 16)`. -/
def rowUEnd : List Instr :=
  [.mov .r6 (.reg .r5), .mov .r4 (.imm 0), .umaal .r6 .r4 .r2 .r9, .mov .r6 (.shifted .r2 .lsr 16),
    .movw .r9 0xffff, .dp .and .r2 .r2 (.reg .r9), .mul .r7 .r1 .r6]

/-- Two words an iteration, then the registers `row` leaves. -/
def rowLoopU : Prog isa :=
  .seq (.block rowUJoin) (.seq (.loop (.block rowBodyU) .ne) (.block rowUEnd))

/-- `row` with `rowLoopU` for its loop. -/
def rowU : Prog isa :=
  .seq (.block (rowSplit ++ rowParity)) (.seq (.ite .ne rowBody (.block []))
    (.seq (.block [.cmp .lr (.imm 0)]) (.seq (.ite .ne rowLoopU (.block [])) (.block rowJoin))))

/-- `c` with each of its rows by `rowU`. -/
def umaalRows (c : Prog isa) : Prog isa := Code.subst row rowU c

end VG.Impl.Bignum.Arm
