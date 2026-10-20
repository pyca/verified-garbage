module

public import VerifiedGarbage.Impl.Bignum.Arm.RowFull
public import VerifiedGarbage.Impl.Bignum.Arm.Shift
public import VerifiedGarbage.Impl.Bignum.Arm.FusedReduction

/-! # A Montgomery round using the temporary array for public loop state

The temporary immediately follows the accumulator's `n + 4` packed words.
Its first eight words hold the count, second operand pointer, modulus pointer,
inverse, current first-operand pointer, remaining rounds, output pointer,
and accumulator pointer. No header or input array is used for spills.
-/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

/-- Enter with `r0` pointing to the temporary. -/
def productArgs : List Instr :=
  [.ldr .r1 .r0 16, .ldr .r1 .r1 0, .ldr .lr .r0 0,
   .ldr .r12 .r0 4, .ldr .r0 .r0 28, .mov .r11 (.imm 0)]

/-- A complete row leaves `r0` sixteen bytes below the temporary. -/
def reductionArgs : List Instr :=
  [.ldr .lr .r0 16, .ldr .r12 .r0 24, .ldr .r1 .r0 28,
   .ldr .r0 .r0 44, .ldr .r2 .r0 0, .mul .r1 .r1 .r2, .mov .r11 (.imm 0)]

def shiftArgs : List Instr :=
  [.ldr .lr .r0 16, .dp .add .lr .lr (.imm 1), .ldr .r0 .r0 44]

/-- After shifting `n + 1` words, clear the vacated word, advance the
first operand pointer, and decrement the public outer-loop count. -/
def clearTop : List Instr :=
  [.mov .r3 (.imm 0), .str .r3 .r0 0, .dp .add .r0 .r0 (.imm 12)]

def advanceOperand : List Instr :=
  [.ldr .r4 .r0 16, .dp .add .r4 .r4 (.imm 4), .str .r4 .r0 16]

def decrementRounds : List Instr :=
  [.ldr .lr .r0 20, .subs .lr .lr (.imm 1), .str .lr .r0 20]

def roundFinish : List Instr := clearTop ++ advanceOperand ++ decrementRounds

def productStage : Prog isa := .seq (.block productArgs) rowFull

def reductionStage : Prog isa := .seq (.block reductionArgs) rowFull

def quotientStage : Prog isa := .seq (.block shiftArgs) (.seq shift (.block roundFinish))

def fusedReductionStage : Prog isa := .seq (.block reductionArgs) FusedReduction.code

def montRound : Prog isa := .seq productStage (.seq fusedReductionStage (.block roundFinish))

def montRounds : Prog isa := .loop montRound .ne

end VG.Impl.Bignum.Arm
