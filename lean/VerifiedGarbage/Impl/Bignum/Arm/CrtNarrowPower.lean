module

public import VerifiedGarbage.Impl.Bignum.Arm.PrepareAcceptedPrime
public import VerifiedGarbage.Impl.Bignum.Arm.SavedOperand
public import VerifiedGarbage.Impl.Bignum.Arm.ReduceOperand
public import VerifiedGarbage.Impl.Bignum.Arm.ClearOperandBuffer
public import VerifiedGarbage.Impl.Bignum.Arm.ActivateWorkspace
public import VerifiedGarbage.Impl.Bignum.Arm.Setup
public import VerifiedGarbage.Impl.Bignum.Arm.ExpControls
public import VerifiedGarbage.Impl.Bignum.Arm.WindowExp
public import VerifiedGarbage.Impl.Bignum.Arm.SubModArray
public import VerifiedGarbage.Impl.Bignum.Arm.MontOp
public import VerifiedGarbage.Impl.Bignum.Arm.CopyBytes

/-! # One CRT factor's private power at the factor's own width

r0 is the factor's full-width workspace, already selected, with the factor in
array 0. The input is imported into its array 1, and its arrays 0 and 6 are
cleared for the results. The narrow workspace after the padded-modulus buffer
is then set up with `max(⌈len/8⌉, ⌈w/2⌉)` limbs, `v`, for the factor's public
byte length and the modulus's `w` limbs, so that `w ≤ 2 v`: it takes the
factor and its own constants, and the safe factor is copied back to array 0.
The input, `x = l + h R` (`R = 2^(64 v)`), is reduced modulo the factor there,
as `l mod M - (0 - h R mod M)`, and raised by the fixed-schedule
exponentiation, whose result is copied back to array 6. Slot 8 holds the main
workspace, whose header gives both workspaces' addresses.
-/

@[expose] public section

namespace VG.Impl.Bignum.Arm.Crt
open VG VG.Arm

/-- The narrow workspace follows the padded modulus buffer of `16 w + 8` bytes,
which stays in r2. -/
def narrowAddress : List Instr :=
  [.ldrSp .r1 8, .ldr .r0 .r1 240, .ldr .r2 .r1 48, .mov .r2 (.shifted .r2 .lsl 4),
   .dp .add .r2 .r2 (.imm 8), .dp .add .r0 .r0 (.reg .r2)]
/-- `max(⌈len/8⌉, ⌈w/2⌉)` limbs for the factor's byte length in the given frame
slot, with r2 `16 w + 8`: `⌈w/2⌉ = (16 w + 16) / 32`, and the larger by a mask. -/
def narrowWidth (lenSlot : Nat) : List Instr :=
  [.ldrSp .r7 lenSlot, .dp .add .r7 .r7 (.imm 7), .mov .r7 (.shifted .r7 .lsr 3),
   .dp .add .r2 .r2 (.imm 8), .mov .r2 (.shifted .r2 .lsr 5),
   .dp .sub .r1 .r7 (.reg .r2), .mov .r1 (.shifted .r1 .lsr 31), .mov .r3 (.imm 0),
   .dp .sub .r1 .r3 (.reg .r1), .dp .sub .r2 .r2 (.reg .r7), .dp .and .r2 .r2 (.reg .r1),
   .dp .add .r7 .r7 (.reg .r2)]
def enterNarrow (lenSlot : Nat) : Prog isa :=
  .seq (.block narrowAddress) (.seq (.block (narrowWidth lenSlot)) (.seq setup (.block activateWorkspace)))
/-- Import the factor again, and prepare it at the narrow width. -/
def narrowPrime (primeSlot : Nat) : Prog isa :=
  .seq (savedOperand 0 primeSlot (primeSlot + 4)) prepareAcceptedPrime

/-! ## Copies between the narrow workspace and a full-width one -/

/-- Array `j` of the full-width workspace linked at main-header byte `slot`, in r1. -/
def fullSource (slot j : Nat) : List Instr := [.ldrSp .r1 8, .ldr .r1 .r1 slot, .ldr .r1 .r1 (64 + 8 * j)]
/-- The narrow array `d` in r0, its `8 v` bytes in lr, and the workspace in r5. -/
def lowArgs (d : Nat) : List Instr :=
  [.ldr .r4 .r0 (64 + 8 * d), .ldr .lr .r0 48, .mov .lr (.shifted .lr .lsl 3), .mov .r5 (.reg .r0), .mov .r0 (.reg .r4)]
/-- The low `v` limbs of the full array `j` into the narrow array `d`. -/
def copyLow (slot j d : Nat) : Prog isa :=
  .seq (.block (fullSource slot j)) (.seq (.block (lowArgs d)) (.seq copyBytes (.block [.mov .r0 (.reg .r5)])))
/-- The source moves up `8 v` bytes; `8 (w - v)` bytes, the main header's `w`
read through r2, into the narrow array `d`; Z when there are none. -/
def highArgs (d : Nat) : List Instr :=
  [.ldr .r2 .r2 48, .ldr .r3 .r0 48, .dp .add .r1 .r1 (.shifted .r3 .lsl 3), .dp .sub .r2 .r2 (.reg .r3),
   .ldr .r4 .r0 (64 + 8 * d), .mov .r5 (.reg .r0), .mov .r0 (.reg .r4), .mov .lr (.shifted .r2 .lsl 3),
   .cmp .lr (.imm 0)]
/-- The limbs of the full array `j` from `v` on, `w - v` of them, into the low
limbs of the (cleared) narrow array `d`. -/
def copyHigh (slot j d : Nat) : Prog isa :=
  .seq (.block (fullSource slot j)) (.seq (.block [.ldrSp .r2 8]) (.seq (.block (highArgs d))
    (.seq (.ite .eq (.block []) copyBytes) (.block [.mov .r0 (.reg .r5)]))))
/-- The narrow array `a` as the source, the full array in r1 as the destination. -/
def outArgs (a : Nat) : List Instr :=
  [.mov .r4 (.reg .r1), .ldr .r1 .r0 (64 + 8 * a), .ldr .lr .r0 48, .mov .lr (.shifted .lr .lsl 3),
   .mov .r5 (.reg .r0), .mov .r0 (.reg .r4)]
/-- The narrow array `a` into the low `v` limbs of the full array `j`. -/
def copyOut (slot j a : Nat) : Prog isa :=
  .seq (.block (fullSource slot j)) (.seq (.block (outArgs a)) (.seq copyBytes (.block [.mov .r0 (.reg .r5)])))

/-- The `w` limbs of the full array `j`, `x = l + h R`, modulo the narrow
modulus into the narrow array 1, with `R² mod M` in array 4: `h` into array 1,
`h R mod M`, its negation into array 6 (array 5 zero), `l` into array 5,
`l mod M`, and the difference. Arrays 2 and 3 are the products' scratch. -/
def reduceHalf (slot j : Nat) : Prog isa :=
  .seq (clearOperandBuffer 72) (.seq (copyHigh slot j 1) (.seq (smallConst 7 1) (.seq (montOp 1 1 4)
    (.seq (clearOperandBuffer 104) (.seq (subModArray 6 5 1) (.seq (copyLow slot j 5)
      (.seq (reduceOperand 5) (subModArray 1 5 6))))))))

def exponentArgs (exponentSlot : Nat) : List Instr := [.ldrSp .r1 exponentSlot, .ldrSp .r2 (exponentSlot + 4)]
def narrowExpWith (phase : Prog isa) (exponentSlot : Nat) : Prog isa :=
  .seq (.block (exponentArgs exponentSlot)) (.seq (.block expControls) phase)

/-- The input into array 1 and cleared arrays 0 and 6 of the selected full workspace. -/
def factorInput : Prog isa :=
  .seq (savedOperand 1 56 12) (.seq (clearOperandBuffer 64) (clearOperandBuffer 112))

/-- `narrowPowerWith`, with the factor prepared by `prime` (`narrowPrime`, or
one given its `R² mod p`). -/
def narrowPowerOf (prime : Nat → Prog isa) (phase : Prog isa) (slot primeSlot exponentSlot : Nat) : Prog isa :=
  .seq factorInput (.seq (enterNarrow (primeSlot + 4)) (.seq (prime primeSlot) (.seq (copyOut slot 0 0)
    (.seq (reduceHalf slot 1) (.seq (narrowExpWith phase exponentSlot) (copyOut slot 6 6))))))

def narrowPowerWith (phase : Prog isa) (slot primeSlot exponentSlot : Nat) : Prog isa :=
  narrowPowerOf narrowPrime phase slot primeSlot exponentSlot

end VG.Impl.Bignum.Arm.Crt
