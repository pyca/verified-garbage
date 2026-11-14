module

public import VerifiedGarbage.Impl.Bignum.Arm.CrtNarrowPower
public import VerifiedGarbage.Impl.Bignum.Arm.R2

/-! # A factor's `R² mod p` from `R² mod n`

In the narrow workspace at the factor's width `v` (`R = 2^(64 v)`), with
the factor `X` in array 0 and `R² mod n` (`w` words, `x = l + h R`) in
array 4 of p's full workspace (main header byte 224): when `w ≤ 2 v`,
`x R⁻²` is `h R⁻¹ + l R⁻²`, three Montgomery multiplications by 1 (`foldReduce`),
which is `2^(64 e) mod X` for `e = 2 (w - v)` when `X` divides `n`; then
doublings to `2^(128 v)`, or, if `e ≤ v`, to `2^(64 v + v)` and six
Montgomery squarings (`r2Squares`): `R² mod X`. For factors of half `n`'s
words, `e = 2 v`: no doublings or squarings. When `2 v < w` (a factor of
fewer than half `n`'s words), `R² mod X` is computed from 1, as `narrowPrime` does
(`r2`). Every branch and count depends only on `w` and `v`.
-/

@[expose] public section

namespace VG.Impl.Bignum.Arm.Crt
open VG VG.Arm

/-- `n`'s words `w` (the main header's, through frame slot 8) into r1 and the
narrow width `v` into r2. -/
def foldWidths : List Instr := [.ldrSp .r1 8, .ldr .r1 .r1 48, .ldr .r2 .r0 48]

/-- Z set iff `w ≤ 2 v`: r3 `= (2 v - w) >>> 31`. -/
def foldTest : List Instr :=
  foldWidths ++ [.dp .add .r3 .r2 (.reg .r2), .dp .sub .r3 .r3 (.reg .r1), .mov .r3 (.shifted .r3 .lsr 31),
    .cmp .r3 (.imm 0)]

/-- Array 4 `:= x R⁻² = h R⁻¹ + l R⁻²` mod `X`: 1 in array 7, `h` into the
cleared array 1, `l` into array 6, array 5 zero. -/
def foldReduce : Prog isa :=
  .seq (smallConst 7 1) (.seq (clearOperandBuffer 104) (.seq (clearOperandBuffer 72)
    (.seq (copyHigh 224 4 1) (.seq (copyLow 224 4 6) (.seq (montOp 1 1 7) (.seq (montOp 6 6 7)
      (.seq (montOp 6 6 7) (.seq (subModArray 4 5 1) (.seq (subModArray 1 6 4) (subModArray 4 1 5))))))))))

/-- `e = 2 (w - v)` into r1, and Z set iff `e ≤ v`. -/
def foldCountArgs : List Instr :=
  foldWidths ++ [.dp .sub .r1 .r1 (.reg .r2), .dp .add .r1 .r1 (.reg .r1), .dp .sub .r3 .r2 (.reg .r1),
    .mov .r3 (.shifted .r3 .lsr 31), .cmp .r3 (.imm 0)]

/-- `e ≤ v`: `64 (v - e) + v` doublings, into header 208. -/
def foldCountLow : List Instr :=
  [.dp .sub .r3 .r2 (.reg .r1), .mov .r3 (.shifted .r3 .lsl 6), .dp .add .r3 .r3 (.reg .r2), .str .r3 .r0 208]

/-- `v < e`: `64 (2 v - e)` doublings. -/
def foldCountHigh : List Instr :=
  [.dp .add .r3 .r2 (.reg .r2), .dp .sub .r3 .r3 (.reg .r1), .mov .r3 (.shifted .r3 .lsl 6), .str .r3 .r0 208]

def foldCounts : Prog isa := .seq (.block foldCountArgs) (.ite .eq (.block foldCountLow) (.block foldCountHigh))

/-- The doublings, if any. -/
def foldDoubles : Prog isa := .seq (.block [.ldr .r1 .r0 208, .cmp .r1 (.imm 0)]) (.ite .eq (.block []) doubleLoop)

/-- The squarings, if `e ≤ v` (tested again from the widths). -/
def foldSquares : Prog isa := .seq (.block foldCountArgs) (.ite .eq r2Squares (.block []))

def r2Fold : Prog isa :=
  .seq foldReduce (.seq (smallConst 7 2) (.seq foldCounts (.seq foldDoubles foldSquares)))

/-- `R² mod X`: from `R² mod n` when `w ≤ 2 v`, else from 1. -/
def r2FromN : Prog isa := .seq (.block foldTest) (.ite .eq r2Fold r2)

/-- The factor imported at the narrow width, accepted or replaced by 3,
and its inverse: `narrowPrime` but its `R² mod X`. -/
def narrowPrimeInv (primeSlot : Nat) : Prog isa :=
  .seq (savedOperand 0 primeSlot (primeSlot + 4)) (.seq (.block installAcceptance)
    (.seq sanitizeModulus precomputeInverse))

/-- `narrowPrime` with `r2FromN`. -/
def narrowPrimeFrom (primeSlot : Nat) : Prog isa := .seq (narrowPrimeInv primeSlot) r2FromN

end VG.Impl.Bignum.Arm.Crt
