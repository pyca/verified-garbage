module

public import VerifiedGarbage.Impl.Bignum.Arm.MontOp
public import VerifiedGarbage.Impl.Bignum.Arm.ShiftLeft

/-!
# Montgomery squaring for ARMv7 RSA

`squareOp o a` writes `a² R⁻¹ mod m` to array `o`, as `montOp o a a` does,
computing each cross product `a_i a_j` (`i < j`) once:

1. `T := 0`, then for `i < n − 1` the row `T[2i+1 …] += a_i · a[i+1 … n−1]`,
   its carry stored into the word `T[i+n]` above it (still zero);
2. `T := 2 T` (one-bit shift);
3. `T[2i], T[2i+1] += a_i²`, with a carry between the pairs: now `T = a²`;
4. `n` reductions in place, `T[i …] += (T[i] m') · m` (`m' = −m⁻¹ mod 2³²`),
   each row's carry added into `T[i+n]` together with the previous round's
   carry `c`, whose own carry is the next `c`;
5. the canonical result from `T[n …] + 2^(32 n) c`, below `2m`, by the
   final subtraction of Montgomery multiplication (`csub`).

The square works in arrays 2 and 3 (the accumulator and temporary), which are
`2n + 8` words of 32 bits for `n` the packed-word count: six words of
metadata at the start of array 2 (`n`, the output, `a`, the operand pointer
or the carry `c`, the count of rows, and the pointer into `T`), then `T`'s
`2n + 2` words. The metadata's address is read from the workspace's header,
through the workspace pointer that the RSA frames keep at `sp` (as
`montOp` uses it); every loop's count and pointers depend only on `n`.
-/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

/-! ## Metadata -/

/-- `r0 :=` the metadata, the start of array 2, from the workspace at `sp`. -/
def sqAnchor : Prog isa := .seq (.block [.ldrSp .r0 0]) (.block [.ldr .r0 .r0 80])

/-- The metadata, from `MontFn.bases`' registers: `r6` the metadata, `r7 = n`,
`r8` the operand and `r10` the output. -/
def sqMeta : List Instr :=
  [.str .r7 .r6 0, .str .r10 .r6 4, .str .r8 .r6 8, .str .r8 .r6 12,
   .dp .sub .r1 .r7 (.imm 1), .str .r1 .r6 16, .dp .add .r1 .r6 (.imm 28), .str .r1 .r6 20]

/-- Clear `T`'s `2n + 2` words. -/
def sqZeroArgs : List Instr :=
  [.dp .add .r0 .r6 (.imm 24), .mov .lr (.shifted .r7 .lsl 1), .dp .add .lr .lr (.imm 2),
   .mov .r3 (.imm 0)]

def sqInit : Prog isa := .seq (.block sqMeta) (.seq (.block sqZeroArgs) zero)

/-! ## Cross products -/

/-- From the metadata in `r0`: the operand pointer `&a[i]` in `r2`, the row's
input `&a[i+1]` in `r12`, the count `n − 1 − i` and the output `&T[2i+1]`;
both pointers advanced in the metadata. -/
def crossArgs : List Instr :=
  [.ldr .r2 .r0 12, .ldr .lr .r0 16, .ldr .r3 .r0 20, .dp .add .r4 .r3 (.imm 8), .str .r4 .r0 20,
   .dp .add .r12 .r2 (.imm 4), .str .r12 .r0 12, .mov .r0 (.reg .r3), .mov .r11 (.imm 0)]

/-- The row's scalar `a_i`. -/
def crossScalar : List Instr := [.ldr .r1 .r2 0]

/-- The row's carry into `T[i+n]`. -/
def crossCarry : List Instr := [.str .r11 .r0 0]

/-- The count of rows decremented: Z after the last. -/
def sqCount : List Instr := [.ldr .lr .r0 16, .subs .lr .lr (.imm 1), .str .lr .r0 16]

def crossRound : Prog isa :=
  .seq sqAnchor (.seq (.block crossArgs) (.seq (.block crossScalar)
    (.seq row (.seq (.block crossCarry) (.seq sqAnchor (.block sqCount))))))

def crossRows : Prog isa := .loop crossRound .ne

/-! ## Doubling -/

def sqDoubleArgs : List Instr :=
  [.ldr .lr .r0 0, .mov .lr (.shifted .lr .lsl 1), .dp .add .r0 .r0 (.imm 24), .mov .r11 (.imm 0)]

def sqDouble : Prog isa := .seq sqAnchor (.seq (.block sqDoubleArgs) shiftLeft)

/-! ## Squares of the words -/

/-- `T[2i], T[2i+1] += a_i² + r11`, the carry out in `r11`; `r12` the operand
word, `r0` the pair. -/
def diagStep : Prog isa :=
  .seq (.block [.ldr .r1 .r12 0, .mov .r2 (.reg .r1), .ldr .r10 .r0 0])
    (.seq (.block mac) (.block [.str .r3 .r0 0, .ldr .r10 .r0 4, .adds .r4 .r4 (.reg .r10),
      .mov .r11 (.imm 0), .adc .r11 .r11 (.imm 0), .str .r4 .r0 4]))

def diagAdvance : List Instr :=
  [.dp .add .r0 .r0 (.imm 8), .dp .add .r12 .r12 (.imm 4), .subs .lr .lr (.imm 1)]

def diagLoop : Prog isa := .loop (.seq diagStep (.block diagAdvance)) .ne

def sqDiagArgs : List Instr :=
  [.ldr .r12 .r0 8, .ldr .lr .r0 0, .dp .add .r0 .r0 (.imm 24), .mov .r11 (.imm 0)]

def sqDiag : Prog isa := .seq sqAnchor (.seq (.block sqDiagArgs) diagLoop)

/-! ## Reduction -/

/-- The carry `c := 0`, the count `n` and the pointer `&T[0]`. -/
def redInit : List Instr :=
  [.ldr .r1 .r0 0, .str .r1 .r0 16, .dp .add .r1 .r0 (.imm 24), .str .r1 .r0 20,
   .mov .r1 (.imm 0), .str .r1 .r0 12]

/-- The modulus and the inverse from the header in `r0`, then the metadata. -/
def redHeader : List Instr := [.ldr .r12 .r0 64, .ldr .r1 .r0 56, .ldr .r0 .r0 80]

/-- The count `n` and the pointer `&T[i]`, advanced in the metadata. -/
def redArgs : List Instr :=
  [.ldr .lr .r0 0, .ldr .r2 .r0 20, .dp .add .r3 .r2 (.imm 4), .str .r3 .r0 20, .mov .r0 (.reg .r2)]

/-- The row's scalar `T[i] m' mod 2³²`. -/
def redScalar : List Instr := [.ldr .r2 .r0 0, .mul .r1 .r1 .r2, .mov .r11 (.imm 0)]

/-- `T[i+n] += r11 + c`, the carry out the next `c`; `r2` the metadata. -/
def redCarry : List Instr :=
  [.ldr .r3 .r0 0, .ldr .r4 .r2 12,
   .adds .r3 .r3 (.reg .r11), .mov .r5 (.imm 0), .adc .r5 .r5 (.imm 0),
   .adds .r3 .r3 (.reg .r4), .adc .r5 .r5 (.imm 0), .str .r3 .r0 0, .str .r5 .r2 12,
   .mov .r0 (.reg .r2)]

def redRound : Prog isa :=
  .seq (.block [.ldrSp .r0 0]) (.seq (.block redHeader) (.seq (.block redArgs) (.seq (.block redScalar)
    (.seq row (.seq (.block [.ldrSp .r2 0]) (.seq (.block [.ldr .r2 .r2 80]) (.seq (.block redCarry)
      (.block sqCount))))))))

def redRounds : Prog isa := .loop redRound .ne

def sqReduce : Prog isa := .seq (.seq sqAnchor (.block redInit)) redRounds

/-! ## The canonical result -/

/-- `T[2n] := c`, then `csub`'s registers: the temporary at the metadata,
the accumulator `&T[n]`, the modulus, the output and the count. -/
def sqFinishHeader : List Instr := [.ldr .r12 .r0 64, .ldr .r0 .r0 80]

def sqFinishLoad : List Instr := [.ldr .r7 .r0 0, .ldr .r9 .r0 4, .ldr .r3 .r0 12]

def sqFinishArgs : List Instr :=
  [.dp .add .r10 .r0 (.shifted .r7 .lsl 3), .str .r3 .r10 24,
   .dp .add .r10 .r0 (.shifted .r7 .lsl 2), .dp .add .r10 .r10 (.imm 24),
   .mov .lr (.reg .r7), .mov .r11 (.imm 0)]

def sqFinish : Prog isa :=
  .seq (.block [.ldrSp .r0 0]) (.seq (.block sqFinishHeader) (.seq (.block sqFinishLoad)
    (.seq (.block sqFinishArgs) csub)))

/-! ## The square -/

def sqBody : Prog isa :=
  .seq sqInit (.seq crossRows (.seq sqDouble (.seq sqDiag (.seq sqReduce sqFinish))))

/-- From the header in `r0`, the output index in `r2` and the operand's in
`r3` and `r12`. -/
def squareBody : Prog isa := .seq (.block MontFn.bases) sqBody

/-- `[o] := [a]² R⁻¹ mod m` inside an RSA frame, as `montOp o a a`. -/
def squareOp (o a : Nat) : Prog isa :=
  .seq (.block (montOpArgs o a a)) (.seq squareBody (.block [.ldrSp .r0 0]))

end VG.Impl.Bignum.Arm
