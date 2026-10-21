module

public import VerifiedGarbage.Impl.Bignum.Arm.PrepareAcceptedPrime
public import VerifiedGarbage.Impl.Bignum.Arm.SavedOperand
public import VerifiedGarbage.Impl.Bignum.Arm.ReduceOperand
public import VerifiedGarbage.Impl.Bignum.Arm.ClearOperandBuffer
public import VerifiedGarbage.Impl.Bignum.Arm.ActivateWorkspace
public import VerifiedGarbage.Impl.Bignum.Arm.Setup
public import VerifiedGarbage.Impl.Bignum.Arm.ExpControls
public import VerifiedGarbage.Impl.Bignum.Arm.WindowExp
public import VerifiedGarbage.Impl.Bignum.Arm.TransferArray

/-! # One CRT factor's private power at the factor's own width

r0 is the factor's full-width workspace, already selected, with the factor in
array 0. Its Montgomery constants reduce the full-width input modulo the
factor, and array 6 is cleared for the result. The narrow workspace after the
padded-modulus buffer is then set up with `max(2, ⌈len/8⌉)` limbs for the
factor's public byte length, takes the factor, its own constants and the
reduced input, and runs the fixed-schedule exponentiation. The result is copied
back into the full-width array 6. Slot 8 holds the main workspace, whose header
gives both workspaces' addresses.
-/

@[expose] public section

namespace VG.Impl.Bignum.Arm.Crt
open VG VG.Arm

/-- The input modulo the prepared factor, at the modulus width. -/
def reduceInput : Prog isa := .seq (savedOperand 1 56 12) (.seq (smallConst 7 1) (reduceOperand 1))
/-- Prepare the factor at the modulus width, reduce the input and clear array 6. -/
def reducePrime : Prog isa := .seq prepareAcceptedPrime (.seq reduceInput (clearOperandBuffer 112))
/-- The narrow workspace follows the padded modulus buffer of `16 w + 8` bytes. -/
def narrowAddress : List Instr :=
  [.ldrSp .r1 8, .ldr .r0 .r1 240, .ldr .r2 .r1 48, .mov .r2 (.shifted .r2 .lsl 4),
   .dp .add .r2 .r2 (.imm 8), .dp .add .r0 .r0 (.reg .r2)]
/-- `max(2, ⌈len/8⌉)` limbs for the factor's byte length in the given frame slot. -/
def narrowWidth (lenSlot : Nat) : List Instr :=
  [.ldrSp .r7 lenSlot, .dp .add .r7 .r7 (.imm 7), .mov .r7 (.shifted .r7 .lsr 3),
   .dp .sub .r1 .r7 (.imm 2), .mov .r1 (.shifted .r1 .lsr 31), .dp .add .r7 .r7 (.reg .r1),
   .mov .r3 (.imm 0)]
def enterNarrow (lenSlot : Nat) : Prog isa :=
  .seq (.block narrowAddress) (.seq (.block (narrowWidth lenSlot)) (.seq setup (.block activateWorkspace)))
/-- Import the factor again, and prepare it at the narrow width. -/
def narrowPrime (primeSlot : Nat) : Prog isa :=
  .seq (savedOperand 0 primeSlot (primeSlot + 4)) prepareAcceptedPrime
/-- Array 1 of the factor's full-width workspace, linked from the main header. -/
def narrowSource (slot : Nat) : List Instr := [.ldrSp .r1 8, .ldr .r1 .r1 slot, .ldr .r1 .r1 72]
def narrowInputArgs : List Instr :=
  [.ldr .r4 .r0 72, .ldr .lr .r0 48, .mov .lr (.shifted .lr .lsl 3), .mov .r5 (.reg .r0), .mov .r0 (.reg .r4)]
/-- Copy the reduced input's low words, as many as the narrow workspace has. -/
def narrowInput (slot : Nat) : Prog isa :=
  .seq (.block (narrowSource slot)) (.seq (.block narrowInputArgs) (.seq copyBytes (.block [.mov .r0 (.reg .r5)])))
def exponentArgs (exponentSlot : Nat) : List Instr := [.ldrSp .r1 exponentSlot, .ldrSp .r2 (exponentSlot + 4)]
def narrowExpWith (phase : Prog isa) (exponentSlot : Nat) : Prog isa :=
  .seq (.block (exponentArgs exponentSlot)) (.seq (.block expControls) phase)
/-- Reselect the factor's full-width workspace, with the narrow one in r1. -/
def narrowExp (exponentSlot : Nat) : Prog isa := narrowExpWith windowExpPhase exponentSlot

def leaveNarrow (slot : Nat) : List Instr := [.mov .r1 (.reg .r0), .ldrSp .r0 8, .ldr .r0 .r0 slot]
def narrowResult (slot : Nat) : Prog isa :=
  .seq (.block (leaveNarrow slot)) (.seq (.block activateWorkspace) (transferArray 6 6))

def narrowPowerWith (phase : Prog isa) (slot primeSlot exponentSlot : Nat) : Prog isa :=
  .seq reducePrime (.seq (enterNarrow (primeSlot + 4)) (.seq (narrowPrime primeSlot) (.seq (narrowInput slot)
    (.seq (narrowExpWith phase exponentSlot) (narrowResult slot)))))

def narrowPower (slot primeSlot exponentSlot : Nat) : Prog isa := narrowPowerWith windowExpPhase slot primeSlot exponentSlot

end VG.Impl.Bignum.Arm.Crt
