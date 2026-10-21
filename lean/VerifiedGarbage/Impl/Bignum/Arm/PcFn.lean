module

public import VerifiedGarbage.Impl.Bignum.Arm.ModulusCheck
public import VerifiedGarbage.Impl.Bignum.Arm.Setup
public import VerifiedGarbage.Impl.Bignum.Arm.Precompute
public import VerifiedGarbage.Impl.Bignum.Arm.PrecomputeOut

/-! # ARMv7 RSA public precomputation entry point

AAPCS arguments are (pre, pre_len, n, n_len, scratch, scratch_len).
The 56-byte frame saves the workspace at 0, pre at 4, n at 8, n_len at 12,
callee-saved registers at 16..44, and lr at 52.
-/

@[expose] public section

namespace VG.Impl.Bignum.Arm.PcFn
open VG VG.Arm

def entry : List Instr :=
  [.addSp .r12 0, .str .r0 .r12 4, .ldrSp .r0 56, .str .r0 .r12 0, .mov .r4 (.reg .r2), .mov .r6 (.reg .r3)]

def head : List Instr := [.dp .add .r7 .r6 (.imm 7), .mov .r7 (.shifted .r7 .lsr 3), .mov .r3 (.imm 0)]
def inputs : List Instr := [.ldrSp .r4 8, .ldrSp .r6 12]

def validWith (arithmetic : Prog isa) : Prog isa := .seq (.block head) (.seq setup (.seq (.block inputs)
  (.seq arithmetic (.seq (.block [.ldrSp .r4 4]) precomputeOut))))

def failArgs : List Instr :=
  [.dp .add .lr .r6 (.imm 7), .mov .lr (.shifted .lr .lsr 3), .mov .lr (.shifted .lr .lsl 2),
   .ldrSp .r0 4, .mov .r3 (.imm 0)]
def fail : Prog isa := .seq (.block failArgs) (.seq zero (.block [.mov .r0 (.imm 0)]))

def valid : Prog isa := validWith precompute

def bodyWith (arithmetic : Prog isa) : Prog isa := .seq (.block modulusCheck) (.ite .eq (validWith arithmetic) fail)

def body : Prog isa := bodyWith precompute

def restore : List Instr :=
  [.ldrSp .r4 16, .ldrSp .r5 20, .ldrSp .r6 24, .ldrSp .r7 28,
   .ldrSp .r8 32, .ldrSp .r9 36, .ldrSp .r10 40, .ldrSp .r11 44, .ldrSp .lr 52]

def codeWith (arithmetic : Prog isa) : Prog isa :=
  .frame (.push [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr])
    (.seq (.block entry) (.seq (bodyWith arithmetic) (.block restore))) (.pop .r12 56)

def code : Prog isa := codeWith precompute

end VG.Impl.Bignum.Arm.PcFn
