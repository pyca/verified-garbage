module

public import VerifiedGarbage.Impl.Bignum.Arm.Square

/-! # One callable Montgomery product and specialized square

The public operand indices choose the dedicated square when they agree.
The first saved stack word is the workspace pointer needed by the square;
the remaining words preserve the procedure-call registers.
-/

@[expose] public section
namespace VG.Impl.Bignum.Arm.MontCall
open VG VG.Arm

def savedRegs : List Reg := [.r0, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr]

def arithmetic : Prog isa := .seq (.block [.cmp .r3 (.reg .r12)])
  (.ite .eq squareBody MontFn.body)

def restore : List Instr :=
  [.ldrSp .r4 4, .ldrSp .r5 8, .ldrSp .r6 12, .ldrSp .r7 16, .ldrSp .r8 20,
    .ldrSp .r9 24, .ldrSp .r10 28, .ldrSp .r11 32, .ldrSp .lr 36]

def code : Prog isa := .frame (.push savedRegs)
  (.seq (.block [.ldrSp .r12 40]) (.seq arithmetic (.block restore))) (.pop .r12 40)

/-- The fifth argument lives in an aligned eight-byte caller frame. The
length passed to the callee covers the eight arithmetic arrays; the caller
may retain further arrays (for example its exponentiation table). -/
def opArgs (o a b : Nat) : List Instr :=
  [.mov .r2 (.imm (BitVec.ofNat 32 o)), .mov .r3 (.imm (BitVec.ofNat 32 a)),
    .mov .lr (.imm (BitVec.ofNat 32 b)), .addSp .r12 0, .str .lr .r12 0,
    .ldr .r1 .r0 48, .dp .add .r1 .r1 (.imm 6), .mov .r1 (.shifted .r1 .lsl 3)]

def op (name : String) (callee : Prog isa) (o a b : Nat) : Prog isa :=
  .seq (.frame (.alloc 8) (.seq (.block (opArgs o a b)) (.call name callee)) (.free 8))
    (.block [.ldrSp .r0 0])

end VG.Impl.Bignum.Arm.MontCall
