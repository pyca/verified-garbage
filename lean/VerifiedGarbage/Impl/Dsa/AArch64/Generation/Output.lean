module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.SeedSearch

/-! Export accepted parameters or zero the caller's output on failure. -/
@[expose] public section
namespace VG.Impl.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Impl.RsaOaep.AArch64

def outputArgs : List Instr :=
  [.ldrSp .x12 40, movi .x3 VG.Impl.Dsa.Generation.Layout.packed, .add .x .x12 .x12 .x3,
   .ldrSp .x2 48, .ldrSp .x9 56]

def outputCopy : Prog isa :=
  .seq (.block outputArgs) (.seq Random.copyRest (.block [movi .x0 1]))

def zeroArgs : List Instr :=
  [.ldrSp .x3 48, .strSp .x3 sOut, .ldrSp .x3 56, .strSp .x3 sK]

def outputZero : Prog isa :=
  .seq (.block zeroArgs) (.seq zeroOut (.block [movi .x0 0]))

def finishOutput : Prog isa :=
  .seq (.block successStatus) (.ite (.zero .x .x3) outputCopy outputZero)

end VG.Impl.Dsa.AArch64.Generation
