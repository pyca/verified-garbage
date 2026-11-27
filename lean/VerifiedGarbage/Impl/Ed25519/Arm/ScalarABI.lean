module

public import VerifiedGarbage.Impl.Ed25519.Arm.Scalar
public import VerifiedGarbage.Impl.Ed25519.Arm.Packed

/-! The zero-stack ARM ABI wrappers for scalar arithmetic. -/

@[expose] public section

namespace VG.Impl.Ed25519.Arm
open VG VG.Arm

abbrev scalarSavedReg := Impl.X25519.Arm.savedReg

def scalarSave (base : Reg) : List Instr :=
  (List.range 8).flatMap fun i => [.str (scalarSavedReg i) base (4 * i)]

def scalarRestore : List Instr :=
  (List.range 8).flatMap fun i => [.ldr (scalarSavedReg i) .r0 (4 * i)]

/-- `out` is kept in `r8`, which the reduction leaves alone: the rows of its
products store through `r7`, an address the taint analysis does not track,
so it would not know a word of the working space to be `out` afterwards. -/
def scalarReduceSetup : List Instr :=
  scalarSave .r2 ++ [.mov .r8 (.reg .r0), .mov .r0 (.reg .r2), .mov .r12 (.reg .r1)]

def scalarFinish : List Instr :=
  [.mov .r12 (.reg .r8)] ++ packField SR 0 ++ scalarRestore

def scalarReduce : Prog isa :=
  .seq (.block scalarReduceSetup) (.seq scalarReduceEngine (.block scalarFinish))

end VG.Impl.Ed25519.Arm
