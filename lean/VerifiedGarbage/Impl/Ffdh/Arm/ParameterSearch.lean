module

public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey

/-! Native safe-prime search over refillable entropy. The first four packed
u64 controller words are attempts, width, entropy cap and request. The
attempt count stays 64 bits: the allowed 8192-bit size starts at 2^32.
Words 4–14 hold consumed bytes, output, used pointer, bits, generator,
tape pointer/length, scratch pointer/length, status and candidate usage.
Only the native routine chooses retries, consumption and refill sizes. -/

@[expose] public section
namespace VG.Impl.Ffdh.Arm.ParameterSearch
open VG VG.Arm

def ldf (r : Reg) (j : Nat) : Instr := .ldr r .r4 (8 * j)
def stf (r : Reg) (j : Nat) : Instr := .str r .r4 (8 * j)

def entry : List Instr := [
  .ldrSp .r4 44, stf .r0 5, stf .r2 6, stf .r3 7,
  .ldrSp .r3 24, stf .r3 8, .ldrSp .r3 28, stf .r3 9,
  .ldrSp .r3 32, stf .r3 10, .ldrSp .r3 36, stf .r3 11,
  .ldrSp .r3 40, stf .r3 12, .mov .r3 (.imm 0), stf .r3 4]

def arguments : List Instr := [
  ldf .r0 5, ldf .r1 1, .dp .add .r2 .r4 (.imm 112), ldf .r3 7, .addSp .r12 0,
  ldf .r9 8, .str .r9 .r12 0, ldf .r9 9, .str .r9 .r12 4,
  ldf .r9 10, .str .r9 .r12 8, ldf .r9 11, .str .r9 .r12 12,
  ldf .r9 12, .str .r9 .r12 16]

def terminal (status : Nat) : List Instr := [
  .mov .r10 (.imm 0), .mov .r11 (.imm (BitVec.ofNat 32 status)),
  stf .r10 0, .str .r10 .r4 4, stf .r10 3, .str .r10 .r4 28, stf .r11 13]

def zeroOut : Prog isa := .seq
  (.block [ldf .r0 5, ldf .lr 1, .mov .r2 (.imm 0)]) Domain.GenerateKey.zeros

def exhausted : Prog isa := .seq (.block (terminal 3)) zeroOut

def acceptHead : List Instr := [
  ldf .r9 14, ldf .r10 4, .dp .add .r10 .r10 (.reg .r9), stf .r10 4]

def accept : List Instr := acceptHead ++ terminal 1

/-- Subtract one from the complete u64 retry counter. `adc` materializes
no-borrow; high := high - 1 + no-borrow. -/
def decrementWords : List Instr := [
  .subs .r9 .r9 (.imm 1), .mov .r12 (.imm 0),
  .adc .r12 .r12 (.imm 0), .dp .sub .r10 .r10 (.imm 1),
  .dp .add .r10 .r10 (.reg .r12)]

def decrement : List Instr := [ldf .r9 0, .ldr .r10 .r4 4] ++
  decrementWords ++ [stf .r9 0, .str .r10 .r4 4]

def rejectHead : List Instr := [
  ldf .r9 14, ldf .r10 4, ldf .r11 9, ldf .r12 10,
  .dp .add .r10 .r10 (.reg .r9), .dp .add .r11 .r11 (.reg .r9),
  .dp .sub .r12 .r12 (.reg .r9), stf .r10 4, stf .r11 9, stf .r12 10]

def reject : List Instr := rejectHead ++
  decrement ++ [.mov .r11 (.imm 4), stf .r11 13]

/-- Z iff r9 < r10, without interpreting an unsigned comparison as signed. -/
def less : List Instr := [
  .subs .r11 .r9 (.reg .r10), .mov .r11 (.imm 0),
  .adc .r11 .r11 (.imm 0), .cmp .r11 (.imm 0)]

def request : Prog isa := .seq
  (.block ([ldf .r9 10, ldf .r10 1, .mov .r10 (.shifted .r10 .lsl 8)] ++ less))
  (.seq (.ite .eq (.block [.mov .r9 (.reg .r10)]) (.block []))
    (.seq (.block ([.dp .add .r9 .r9 (.reg .r9), ldf .r10 2] ++ less))
      (.seq (.ite .eq (.block []) (.block [.mov .r9 (.reg .r10)]))
        (.block [stf .r9 3, .mov .r11 (.imm 0), .str .r11 .r4 28, stf .r11 13]))))

def short : Prog isa := .seq (.block ([ldf .r9 10, ldf .r10 2] ++ less))
  (.ite .eq request exhausted)

def classify : Prog isa := .seq (.block [.cmp .r0 (.imm 1)])
  (.ite .eq (.block accept) (.seq (.block [.cmp .r0 (.imm 2)])
    (.ite .eq (.block reject) short)))

def candidateRun (candidate : Prog isa) : Prog isa :=
  .frame (.alloc 24) (.seq (.block arguments) candidate) (.free 24)

def budgetGuard : List Instr := [.dp .orr .r9 .r9 (.reg .r10), .cmp .r9 (.imm 0)]

/-- Do not call the candidate with a depleted tape. A tape shorter than
one modulus cannot contain a candidate; clear the output and request its
replacement directly, keeping pointer arithmetic away from an empty tail. -/
def candidateStep (candidate : Prog isa) : Prog isa := .seq
  (.block ([ldf .r9 10, ldf .r10 1] ++ less))
  (.ite .eq (.seq zeroOut request) (.seq (candidateRun candidate) classify))

def iteration (candidate : Prog isa) : Prog isa := .seq
  (.block ([ldf .r9 0, .ldr .r10 .r4 4] ++ budgetGuard))
  (.seq (.ite .eq exhausted (candidateStep candidate))
    (.block [ldf .r9 13, .cmp .r9 (.imm 4)]))

def finish : List Instr := [
  ldf .r1 6, ldf .r2 4, ldf .r0 13, .mov .r3 (.imm 0), .str .r2 .r1 0, .str .r3 .r1 4,
  .ldrSp .r9 4, .ldrSp .r10 8, .ldrSp .r11 12, .ldrSp .lr 20]

def code (candidate : Prog isa) : Prog isa := .frame (.push [.r4, .r9, .r10, .r11, .r12, .lr])
  (.seq (.block entry) (.seq (.loop (iteration candidate) .eq) (.block finish))) (.pop .r4 24)

end VG.Impl.Ffdh.Arm.ParameterSearch
