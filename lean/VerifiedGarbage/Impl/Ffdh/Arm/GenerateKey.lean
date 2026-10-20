module

public import VerifiedGarbage.Impl.Ffdh.Arm.Domain

/-! One native FFDH key-generation attempt: public-bound scanning, entropy
masking, private/public checks and output clearing all execute on ARMv7. -/

@[expose] public section
namespace VG.Impl.Ffdh.Arm.Domain.GenerateKey
open VG VG.Arm VG.Impl.Bignum.Arm

/-- The loop continues only when a public leading zero was skipped. -/
def advance : Prog isa := .block [
  .dp .add .r4 .r4 (.imm 1), .dp .sub .r6 .r6 (.imm 1),
  .mov .r11 (.imm 1), .cmp .r11 (.imm 0)]
def stop : Prog isa := .block [.mov .r11 (.imm 0), .cmp .r11 (.imm 0)]
def scanStep : Prog isa := .seq (.block [.ldrb .r3 .r4 0, .cmp .r3 (.imm 0)])
  (.ite .eq (.seq (.block [.cmp .r6 (.imm 1)]) (.ite .ne advance stop)) stop)
def scan : Prog isa := .loop scanStep .ne

def smear : List Instr := [
  .mov .r12 (.shifted .r3 .lsr 1), .dp .orr .r3 .r3 (.reg .r12),
  .mov .r12 (.shifted .r3 .lsr 2), .dp .orr .r3 .r3 (.reg .r12),
  .mov .r12 (.shifted .r3 .lsr 4), .dp .orr .r3 .r3 (.reg .r12)]

def boundArgs : Prog isa := .seq (withQ (.block [.ldrSp .r4 60]) (.block [.ldrSp .r4 24]))
  (.block [.ldrSp .r6 32])

def boundSave : List Instr := [.addSp .r12 0, st .r6 20, st .r3 68]

/-- p and p-1 have the same bit length for every valid odd p>2. -/
def bound : Prog isa := .seq boundArgs (.seq scan (.block (smear ++ boundSave)))

/-- Skip a zero byte count without branching on any secret. -/
def unlessZero (r : Reg) (body : Prog isa) : Prog isa :=
  .seq (.block [.cmp r (.imm 0)]) (.ite .eq (.block []) body)

def zeroStep : List Instr := [
  .strb .r2 .r0 0, .dp .add .r0 .r0 (.imm 1), .subs .lr .lr (.imm 1)]
def zeros : Prog isa := .loop (.block zeroStep) .ne

def prefixStep : List Instr := [
  .strb .r2 .r0 0, .dp .add .r0 .r0 (.imm 1),
  .dp .add .r1 .r1 (.imm 1), .subs .lr .lr (.imm 1)]

def first : List Instr := [
  .ldrb .r2 .r1 0, .ldrSp .r3 68, .dp .and .r2 .r2 (.reg .r3), .strb .r2 .r0 0,
  .dp .add .r0 .r0 (.imm 1), .dp .add .r1 .r1 (.imm 1), .ldrSp .lr 20, .dp .sub .lr .lr (.imm 1)]

/-- Entropy is cut to the public bound's bit length without inspecting any
secret leading byte. The significant scalar pointer is kept at offset 16. -/
def scalarArgs : List Instr := [
  .ldrSp .r0 40, .ldrSp .r1 48, .ldrSp .lr 32, .ldrSp .r3 20,
  .dp .sub .lr .lr (.reg .r3), .dp .add .r3 .r0 (.reg .lr), .addSp .r12 0, st .r3 16,
  .mov .r2 (.imm 0)]

def cutEntropy : Prog isa := .seq (unlessZero .lr (.loop (.block prefixStep) .ne))
  (.seq (.block first) (unlessZero .lr copyBytes))

def scalar : Prog isa := .seq bound (.seq (.block scalarArgs)
  (.seq cutEntropy (.block [.ldrSp .r0 0])))

def clearOutput (slot : Nat) : Prog isa := .seq (.block [
  .ldrSp .r0 slot, .ldrSp .lr 32, .mov .r2 (.imm 0)]) zeros

def failScalar : Prog isa := .seq (clearOutput 40) (.seq (clearOutput 36) (ret 2))

def maskOutput (slot : Nat) : Prog isa := .seq (.block [
  .ldrSp .r0 slot, .ldrSp .lr 32, .ldrSp .r3 64,
  .mov .r2 (.imm 0), .dp .sub .r2 .r2 (.reg .r3)]) maskBytes

/-- A power of a valid domain's generator is already in its subgroup. Only
its nondegenerate range needs checking after exponentiation. -/
def finish : Prog isa := .seq (maskOutput 40) (.seq (maskOutput 36) (.block [
  .ldrSp .r3 64, .mov .r0 (.imm 3), .dp .sub .r0 .r0 (.shifted .r3 .lsl 1)]))

def tail : Prog isa := .seq (powerAt 56 16 20) (.seq (inRange 6)
  (.seq (.block Exchange.saveResult) (.seq Exchange.exportResult finish)))

def main : Prog isa := .seq (prepareAt 24) (.seq scalar (.seq (importAt 1 40 44)
  (.seq CheckPrivate.scalarRange (ifFlag tail failScalar))))

def entry : List Instr := [
  .addSp .r12 0, st .r0 40, st .r2 36, st .r2 4,
  .ldrSp .r3 128, st .r3 24, .ldrSp .r3 132, st .r3 28,
  .ldrSp .r3 136, st .r3 32, st .r3 44, .ldrSp .r3 140, st .r3 48,
  .ldrSp .r0 148, st .r0 0]

def code : Prog isa := framed (.seq (.block entry) (head main))

end VG.Impl.Ffdh.Arm.Domain.GenerateKey
