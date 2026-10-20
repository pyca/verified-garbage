module
public import VerifiedGarbage.Impl.Mont.Arm.Dynamic


/-! # Branch-free integer checks for DSA components on 32-bit ARM

Each check leaves a mask in `r2`: all ones or zero. Comparisons run a borrow
chain over 16-bit digits, as the arithmetic does.
-/

@[expose] public section
namespace VG.Impl.Dsa.Arm
open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic

/-- `r4 = 0 - 1`, all ones. -/
def allOnes : List Instr := [.mov .r4 (.imm 0), .dp .sub .r4 .r4 (.imm 1)]

/-- `r2` all ones if `[a]` (`k > 0` words) is nonzero, else zero. -/
def nonzero (k a : Nat) : Prog isa :=
  .seq (.block ([.mov .r3 (.imm 0)] ++ ptr .r10 a ++ ptr .r9 (a + 4 * k))) <|
  .seq (ptrLoop .r10 [.ldr .r4 .r10 0, .dp .orr .r3 .r3 (.reg .r4), bump .r10 4])
    (.block [.mov .r4 (.imm 0), .dp .sub .r4 .r4 (.reg .r3), .dp .orr .r4 .r4 (.reg .r3),
      .mov .r4 (.shifted .r4 .lsr 31), .mov .r2 (.imm 0), .dp .sub .r2 .r2 (.reg .r4)])

/-- Digit `h` of `[a] - [b]` (words in `r7`, `r5`), from the carry `r3` (1:
no borrow), its carry to `r3`; the digit stays in `r4`. -/
def borrowDigit (h : Nat) : List Instr :=
  [half .r4 .r7 h, .dp .add .r4 .r4 (.reg .r6), half .r0 .r5 h, .dp .sub .r4 .r4 (.reg .r0),
    .dp .add .r4 .r4 (.reg .r3), .mov .r3 (.shifted .r4 .lsr 16)]

/-- `r2` all ones if `[a] < [b]` (`k > 0` words), else zero. -/
def lessThan (k a b : Nat) : Prog isa :=
  .seq (.block ([mask16, .mov .r3 (.imm 1)] ++ ptr .r10 a ++ ptr .r1 b ++ ptr .r9 (a + 4 * k))) <|
  .seq (ptrLoop .r10 ([.ldr .r7 .r10 0, .ldr .r5 .r1 0] ++ borrowDigit 0 ++ borrowDigit 1 ++
      [bump .r10 4, bump .r1 4]))
    (.block [.dp .sub .r2 .r3 (.imm 1)])

/-- `[o] = [a] - [b]`, `k > 0` words, packed (the borrow is dropped). -/
def subWords (k o a b : Nat) : Prog isa :=
  .seq (.block ([mask16, .mov .r3 (.imm 1)] ++ ptr .r10 a ++ ptr .r1 b ++ ptr .r8 o ++ ptr .r9 (a + 4 * k))) <|
  ptrLoop .r10 ([.ldr .r7 .r10 0, .ldr .r5 .r1 0] ++ borrowDigit 0 ++ [.dp .and .r2 .r4 (.reg .r6)] ++
    borrowDigit 1 ++ [.dp .orr .r2 .r2 (.shifted .r4 .lsl 16), .str .r2 .r8 0, bump .r10 4, bump .r1 4,
      bump .r8 4])

/-- `r2` all ones if `[a] = [b]` (`k > 0` words), from two comparisons. -/
def equal (k a b : Nat) : Prog isa :=
  .seq (lessThan k a b) <| .seq (.block [.mov .r8 (.reg .r2)]) <| .seq (lessThan k b a)
    (.block ([.dp .orr .r2 .r2 (.reg .r8)] ++ allOnes ++ [.dp .eor .r2 .r2 (.reg .r4)]))

/-- `[flag] &= r2`. -/
def andFlag (flag : Nat) : List Instr :=
  [.ldr .r4 .r12 flag, .dp .and .r4 .r4 (.reg .r2), .str .r4 .r12 flag]

/-- `[flag] &=` whether `0 < [a] < [m]`. -/
def checkRange (k a m flag : Nat) : Prog isa :=
  .seq (lessThan k a m) <| .seq (.block [.mov .r8 (.reg .r2)]) <| .seq (nonzero k a)
    (.block (.dp .and .r2 .r2 (.reg .r8) :: andFlag flag))

/-- `[flag] &=` whether `[a]` is nonzero (or zero). -/
def checkZero (k a flag : Nat) (wantNonzero : Bool) : Prog isa :=
  .seq (nonzero k a)
    (.block ((if wantNonzero then [] else allOnes ++ [.dp .eor .r2 .r2 (.reg .r4)]) ++ andFlag flag))

/-- `r2` all ones if `[a] < x` (`k` words, through `[tmp]`). -/
def lessThanConstant (k a tmp x : Nat) : Prog isa :=
  .seq (setConst k tmp x) (lessThan k a tmp)

/-- `r2` all ones exactly when `2^(bits-1) ≤ [a] < 2^bits` (`2n` words); for
a full-width value the upper bound is its storage width. -/
def widthMask (n a tmp bits : Nat) : Prog isa :=
  .seq (lessThanConstant (2 * n) a tmp (2 ^ (bits - 1))) <|
  .seq (.block (allOnes ++ [.dp .eor .r2 .r2 (.reg .r4), .mov .r11 (.reg .r2)]))
  (if bits < 64 * n then
    .seq (lessThanConstant (2 * n) a tmp (2 ^ bits)) (.block [.dp .and .r2 .r2 (.reg .r11)])
   else .block [.mov .r2 (.reg .r11)])

/-- A supported width larger than the buffer cannot match. -/
def optionalWidth (n a tmp bits : Nat) : Prog isa :=
  if bits ≤ 64 * n then widthMask n a tmp bits else .block [.mov .r2 (.imm 0)]

end VG.Impl.Dsa.Arm
