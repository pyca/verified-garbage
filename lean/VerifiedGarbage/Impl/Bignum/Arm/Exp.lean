module

public import VerifiedGarbage.Impl.Bignum.Arm.R2

/-! # RSA exponentiation in Montgomery form -/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

/-- Ordinary one, the running Montgomery one, and the encoded input. -/
def expInit : Prog isa :=
  .seq (smallConst 7 1) (.seq (montOp 6 4 7) (montOp 5 1 4))

/-- Bit 7 of the shifted exponent byte, kept at header offset 200. -/
def expBitTest : List Instr :=
  [.ldr .r1 .r0 200, .mov .r1 (.shifted .r1 .lsr 7), .dp .and .r1 .r1 (.imm 1), .subs .r1 .r1 (.imm 0)]

/-- Process the current public exponent bit. -/
def expBit : Prog isa :=
  .seq (squareOp 6 6) (.seq (.block expBitTest) (.ite .ne (montOp 6 6 5) (.block [])))

/-- Advance the byte and its remaining bit count. -/
def expShift : List Instr := [.ldr .r1 .r0 200, .dp .add .r1 .r1 (.reg .r1), .str .r1 .r0 200]
def expDecrement : List Instr := [.ldr .r1 .r0 192, .subs .r1 .r1 (.imm 1), .str .r1 .r0 192]
def expBitRound : Prog isa := .seq expBit (.seq (.block expShift) (.block expDecrement))
def expBits : Prog isa := .loop expBitRound .ne

/-- Current exponent-byte pointer at 128 and remaining byte count at 132. -/
def expByteLoad : List Instr := [.ldr .r2 .r0 128, .ldrb .r1 .r2 0]
def expByteSave : List Instr := [.str .r1 .r0 200, .mov .r1 (.imm 8), .str .r1 .r0 192]
def expByteHead : Prog isa := .block (expByteLoad ++ expByteSave)
def expByteNext : List Instr :=
  [.ldr .r1 .r0 128, .dp .add .r1 .r1 (.imm 1), .str .r1 .r0 128,
   .ldr .r1 .r0 132, .subs .r1 .r1 (.imm 1), .str .r1 .r0 132]
def expBytes : Prog isa := .loop (.seq expByteHead (.seq expBits (.block expByteNext))) .ne

/-- Encode the input, scan the exponent bytes, then convert back to ordinary form. -/
def expPhase : Prog isa := .seq expInit (.seq expBytes (montOp 6 6 7))

end VG.Impl.Bignum.Arm
