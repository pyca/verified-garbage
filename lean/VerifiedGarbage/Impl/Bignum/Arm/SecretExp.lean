module

public import VerifiedGarbage.Impl.Bignum.Arm.Exp
public import VerifiedGarbage.Impl.Bignum.Arm.SelectPower

/-! # Fixed-schedule Montgomery exponentiation for private RSA exponents -/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

/-- The secret bit is used only as a word-selection mask. -/
def secretBitValue : List Instr :=
  [.ldr .r11 .r0 200, .mov .r11 (.shifted .r11 .lsr 7), .dp .and .r11 .r11 (.imm 1)]

def secretExpBit : Prog isa :=
  .seq (montOp 6 6 6) (.seq (montOp 1 6 5) (.seq (.block secretBitValue) selectPower))
def secretExpRound : Prog isa := .seq secretExpBit (.seq (.block expShift) (.block expDecrement))
def secretExpBits : Prog isa := .loop secretExpRound .ne
def secretExpBytes : Prog isa := .loop (.seq expByteHead (.seq secretExpBits (.block expByteNext))) .ne
def secretExpPhase : Prog isa := .seq expInit (.seq secretExpBytes (montOp 6 6 7))

end VG.Impl.Bignum.Arm
