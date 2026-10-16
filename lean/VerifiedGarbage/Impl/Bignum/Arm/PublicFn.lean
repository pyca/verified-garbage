module

public import VerifiedGarbage.Impl.Bignum.Arm.PcFn
public import VerifiedGarbage.Impl.Bignum.Arm.ExponentCheck
public import VerifiedGarbage.Impl.Bignum.Arm.ImportOperand
public import VerifiedGarbage.Impl.Bignum.Arm.InputCompare
public import VerifiedGarbage.Impl.Bignum.Arm.SaveAcceptance
public import VerifiedGarbage.Impl.Bignum.Arm.ExpControls
public import VerifiedGarbage.Impl.Bignum.Arm.Exp
public import VerifiedGarbage.Impl.Bignum.Arm.ExportMasked

/-! # ARMv7 checked public RSA operation

AAPCS arguments: (out, out_len, n, n_len, e, e_len, input, input_len,
scratch, scratch_len). The frame is 56 bytes. Only public key validation
branches; the secret input comparison is saved at frame offset 48 and
applied as an output mask after exponentiation.
-/

@[expose] public section

namespace VG.Impl.Bignum.Arm.PublicFn
open VG VG.Arm

def entry : List Instr :=
  [.addSp .r12 0, .str .r0 .r12 4, .ldrSp .r0 72, .str .r0 .r12 0]

def exponentArgs : List Instr := [.ldrSp .r1 56, .ldrSp .lr 60]
def inputArgs : List Instr := [.ldrSp .r4 64, .ldrSp .r6 12]
def controlArgs : List Instr := [.ldrSp .r1 56, .ldrSp .r2 60]
def outputArgs : List Instr := [.mov .r2 (.imm 6), .ldrSp .r4 4, .ldrSp .r6 12]

def importInput : Prog isa := .seq (.block inputArgs) (importOperand 1)
def acceptInput : Prog isa := .seq inputCompare (.block saveAcceptance)
def controls : Prog isa := .seq (.block controlArgs) (.block expControls)
def finish : Prog isa := .seq (.block outputArgs) exportMasked

def applyInput : Prog isa :=
  .seq importInput (.seq acceptInput (.seq controls (.seq expPhase finish)))

def prepare : Prog isa := .seq (.block PcFn.head) (.seq setup (.block PcFn.inputs))

def valid : Prog isa := .seq prepare (.seq precompute applyInput)

def failArgs : List Instr := [.ldrSp .r0 4, .ldrSp .lr 12, .mov .r2 (.imm 0)]
def fail : Prog isa := .seq (.block failArgs) (.seq maskBytes (.block [.mov .r0 (.imm 0)]))

def modulus : Prog isa := .seq (.block PcFn.inputs)
  (.seq (.block modulusCheck) (.ite .eq valid fail))

def body : Prog isa := .seq (.block exponentArgs) (.seq exponentCheck
  (.seq (.block [.subs .r7 .r7 (.imm 0)]) (.ite .eq fail modulus)))

def code : Prog isa :=
  .frame (.push [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr])
    (.seq (.block entry) (.seq body (.block PcFn.restore))) (.pop .r12 56)

end VG.Impl.Bignum.Arm.PublicFn
