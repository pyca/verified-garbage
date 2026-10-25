module

public import VerifiedGarbage.TCB.PPC64LE.Isa

/-! # Native FFDH parameter generation on PPC64LE: validation and limits

`vg_ffdh_parameter_generation_init(state = r3, bits = r4, generator = r5)`.
The comparisons are the sign bits of 64-bit differences of small numbers,
without the carry bit: `bits` is first checked to be below `2^14`
(its bits from 14 up zero), a branch on a public value; then, with
`lt c` the sign bit of `x − c`, 1 exactly when `x < c`,

* `r12 := lt 8193 − lt 512` for `bits`, 1 exactly when `512 ≤ bits ≤ 8192`;
* `r7 := (lt 3 − lt 2) + (lt 6 − lt 5)` for the generator's low word,
  zero-extended, 1 exactly when it is 2 or 5;

and `r12 := r12 · r7`. Then the attempt limit `bits² · 64`, the width
`⌈bits / 8⌉`, the entropy cap `32769 ⌈bits / 8⌉` and the first request
`512 ⌈bits / 8⌉`, and 1 returned, or zeros to the four public words and 0
returned.
-/

@[expose] public section

namespace VG.Impl.Ffdh.PPC64LE.Generation

open VG VG.PPC64LE

/-- `r12 := bits >> 14`, zero exactly for `bits < 2^14`. -/
def high : List Instr := [.lsr .d .r12 .r4 14]

/-- `d := 1` if `n < c`, else 0, for `n` and `c` below `2^63`. -/
def lt (d n : Reg) (c : Nat) : List Instr := [.li .r9 c, .sub d n .r9, .lsr .d d d 63]

/-- With `bits < 2^14`: `r12 := 1` exactly when `512 ≤ bits ≤ 8192` and the
generator, zero-extended into `r6`, is 2 or 5, else 0. -/
def validate : List Instr :=
  lt .r10 .r4 512 ++ lt .r11 .r4 8193 ++ [.sub .r12 .r11 .r10, .lsr .w .r6 .r5 0] ++
  lt .r7 .r6 2 ++ lt .r8 .r6 3 ++ [.sub .r7 .r8 .r7] ++
  lt .r8 .r6 5 ++ lt .r10 .r6 6 ++ [.sub .r8 .r10 .r8, .add .r7 .r7 .r8, .mul .r12 .r12 .r7]

/-- Zeros to the four public words, and 0 returned. -/
def clear : List Instr := [
  .li .r9 0, .store .d .r9 .r3 0, .store .d .r9 .r3 8, .store .d .r9 .r3 16, .store .d .r9 .r3 24,
  .li .r3 0]

/-- The four public words, and 1 returned. -/
def initializeState : List Instr := [
  .mul .r9 .r4 .r4, .lsl .r9 .r9 6, .addi .r10 .r4 7, .lsr .d .r10 .r10 3,
  .lsl .r11 .r10 15, .add .r11 .r11 .r10, .lsl .r12 .r10 9,
  .store .d .r9 .r3 0, .store .d .r10 .r3 8, .store .d .r11 .r3 16, .store .d .r12 .r3 24, .li .r3 1]

def init : Prog isa :=
  .seq (.block high)
    (.ite (.zero .d .r12)
      (.seq (.block validate) (.ite (.zero .d .r12) (.block clear) (.block initializeState)))
      (.block clear))

end VG.Impl.Ffdh.PPC64LE.Generation
