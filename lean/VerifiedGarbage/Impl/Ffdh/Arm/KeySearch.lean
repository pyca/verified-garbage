module

public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey

/-! The native ARMv7 FFDH key-generation controller. Four packed-u64 public
words hold the two bounded retry counters, width, and next entropy request;
the last twelve words retain arguments across calls. r4 holds the controller
pointer and is preserved by the selected key-generation attempt. The outer
frame saves r4, r9–r11 and lr; each attempt allocates its seven stack arguments. -/

@[expose] public section
namespace VG.Impl.Ffdh.Arm.KeySearch
open VG VG.Arm

def ldf (r : Reg) (j : Nat) : Instr := .ldr r .r4 (8 * j)
def stf (r : Reg) (j : Nat) : Instr := .str r .r4 (8 * j)

def entry : List Instr := [
  .ldrSp .r4 56, stf .r0 5, stf .r2 6,
  .ldrSp .r3 24, stf .r3 15,
  .ldrSp .r3 28, stf .r3 7, .ldrSp .r3 32, stf .r3 8,
  .ldrSp .r3 40, stf .r3 9, .ldrSp .r3 44, stf .r3 10,
  .ldrSp .r3 48, stf .r3 12, .ldrSp .r3 52, stf .r3 13,
  .mov .r3 (.imm 0), stf .r3 11]

def arguments : List Instr := [
  ldf .r0 5, ldf .r1 2, ldf .r2 6, ldf .r3 2, .addSp .r12 0,
  ldf .r9 7, .str .r9 .r12 0, ldf .r9 8, .str .r9 .r12 4,
  .str .r1 .r12 8, ldf .r9 9, .str .r9 .r12 12, .str .r1 .r12 16,
  ldf .r9 12, .str .r9 .r12 20, ldf .r9 13, .str .r9 .r12 24]

def terminal (status : Nat) : List Instr := [
  .mov .r10 (.imm 0), .mov .r11 (.imm (BitVec.ofNat 32 status)),
  stf .r10 0, stf .r10 1, stf .r10 3, .str .r10 .r4 28, stf .r11 14]

def zeroOutput (slot : Nat) : Prog isa := .seq (.block [
  ldf .r0 slot, ldf .lr 2, .mov .r2 (.imm 0)]) Domain.GenerateKey.zeros

def zeroOutputs : Prog isa := .seq (zeroOutput 5) (zeroOutput 6)
def exhausted : Prog isa := .seq (.block (terminal 3)) zeroOutputs

def advanceLoads : List Instr := [
  .mov .r9 (.reg .r0), ldf .r10 2, ldf .r11 9, ldf .r12 10, ldf .r3 11]

def advanceUpdate : List Instr := [
  .dp .add .r11 .r11 (.reg .r10), .dp .sub .r12 .r12 (.reg .r10), .dp .add .r3 .r3 (.reg .r10),
  stf .r11 9, stf .r12 10, stf .r3 11]

def advance : List Instr := advanceLoads ++ advanceUpdate

def rejectedScalar : List Instr := [
  ldf .r10 1, .dp .sub .r10 .r10 (.imm 1), .mov .r11 (.imm 4), stf .r10 1, stf .r11 14]

def rejectedPublic : List Instr := [
  ldf .r10 0, .dp .sub .r10 .r10 (.imm 1), .mov .r11 (.imm 128), .mov .r12 (.imm 4),
  stf .r10 0, stf .r11 1, stf .r12 14]

def classify : Prog isa := .seq (.block (advance ++ [.cmp .r9 (.imm 1)]))
  (.ite .eq (.block (terminal 1)) (.seq (.block [.cmp .r9 (.imm 2)])
    (.ite .eq (.block rejectedScalar) (.seq (.block [.cmp .r9 (.imm 3)])
      (.ite .eq (.block rejectedPublic) exhausted)))))

def request : Prog isa := .seq (.block [
  ldf .r10 2, .mov .r11 (.imm 0), stf .r10 3, .str .r11 .r4 28, stf .r11 14]) zeroOutputs

/-- Turn the public unsigned length comparison into a branch flag. -/
def room : List Instr := [
  ldf .r9 10, ldf .r10 2, .subs .r11 .r9 (.reg .r10), .mov .r11 (.imm 0),
  .adc .r11 .r11 (.imm 0), .cmp .r11 (.imm 0)]

def attemptRun (attempt : Prog isa) : Prog isa :=
  .frame (.alloc 32) (.seq (.block arguments) attempt) (.free 32)

def attemptOrRequest (attempt : Prog isa) : Prog isa := .seq (.block room)
  (.ite .eq request (.seq (attemptRun attempt) classify))

def branch (attempt : Prog isa) : Prog isa := .ite .eq exhausted
  (.seq (.block [ldf .r9 1, .cmp .r9 (.imm 0)]) (.ite .eq exhausted (attemptOrRequest attempt)))

def iteration (attempt : Prog isa) : Prog isa := .seq (.block [ldf .r9 0, .cmp .r9 (.imm 0)])
  (.seq (branch attempt) (.block [ldf .r9 14, .cmp .r9 (.imm 4)]))

def finish : List Instr := [
  ldf .r1 15, ldf .r2 11, ldf .r0 14, .mov .r3 (.imm 0), .str .r2 .r1 0, .str .r3 .r1 4,
  .ldrSp .r9 4, .ldrSp .r10 8, .ldrSp .r11 12, .ldrSp .lr 20]

def code (attempt : Prog isa) : Prog isa := .frame (.push [.r4, .r9, .r10, .r11, .r12, .lr])
  (.seq (.block entry) (.seq (.loop (iteration attempt) .eq) (.block finish))) (.pop .r4 24)

end VG.Impl.Ffdh.Arm.KeySearch
