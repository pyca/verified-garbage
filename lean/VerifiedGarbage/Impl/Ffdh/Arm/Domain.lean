module

public import VerifiedGarbage.Impl.Bignum.Arm.ImportOperand
public import VerifiedGarbage.Impl.Bignum.Arm.ModulusCheck
public import VerifiedGarbage.Impl.Bignum.Arm.MaskBytes
public import VerifiedGarbage.Impl.Ffdh.Arm.Checks
public import VerifiedGarbage.Impl.Bignum.Arm.ReduceOperand
public import VerifiedGarbage.Impl.Bignum.Arm.ExportBE
public import VerifiedGarbage.Impl.Ffdh.Arm.Arithmetic

/-! FFDH domain operations over the runtime-sized ARMv7 RSA workspace.
The 72-byte local frame contains pointers, public lengths and saved flags.
All arithmetic arrays retain RSA's shared packed-u64 representation. -/

@[expose] public section
namespace VG.Impl.Ffdh.Arm.Domain
open VG VG.Arm VG.Impl.Bignum.Arm

-- Local offsets: workspace 0; output 4; modulus input/count 8/12;
-- domain 24/28; p length 32; public 36; private 40/44;
-- entropy 48; g 56; q 60; result flag 64.
def st (r : Reg) (d : Nat) : Instr := .str r .r12 d

def ret (n : BitVec 32) : Prog isa := .block [.mov .r0 (.imm n)]
def testFlag : Prog isa := .block [.cmp .r11 (.imm 0)]
def ifFlag (yes no : Prog isa) : Prog isa := .seq testFlag (.ite .ne yes no)

def qTest : Prog isa := .block [
  .ldrSp .r3 28, .ldrSp .r4 32, .dp .sub .r3 .r3 (.reg .r4),
  .dp .sub .r3 .r3 (.reg .r4), .cmp .r3 (.imm 0)]
def withQ (yes no : Prog isa) : Prog isa := .seq qTest (.ite .ne yes no)

/-- Retain the modulus pointer/count for RSA's preparation helper. -/
def prepareArgs (slot : Nat) : List Instr := [
  .ldrSp .r4 slot, .ldrSp .r6 32, .addSp .r12 0, st .r4 8, st .r6 12]
def prepareAt (slot : Nat) : Prog isa :=
  .seq (.block (prepareArgs slot)) VG.Impl.Ffdh.Arm.prepare

def importArgs (slot countSlot : Nat) : List Instr := [.ldrSp .r4 slot, .ldrSp .r6 countSlot]

def importAt (a slot countSlot : Nat) : Prog isa :=
  .seq (.block (importArgs slot countSlot)) (importOperand a)

/-- Both the base and public q are padded to p_len. Private exponents keep
all supplied bytes, including leading zeroes. -/
def powerArgs (baseSlot exponentSlot exponentLength : Nat) : List Instr := [
  .ldrSp .r4 baseSlot, .ldrSp .r6 32, .ldrSp .r1 exponentSlot, .ldrSp .r2 exponentLength]

def powerAt (baseSlot exponentSlot exponentLength : Nat) : Prog isa :=
  .seq (.block (powerArgs baseSlot exponentSlot exponentLength)) VG.Impl.Ffdh.Arm.power

def subgroup (baseSlot : Nat) : Prog isa :=
  .seq (powerAt baseSlot 60 32) (VG.Impl.Ffdh.Arm.isOne 6)

def domainPointers : List Instr := [
  .dp .add .r3 .r4 (.reg .r6), st .r3 56,
  .dp .add .r3 .r3 (.reg .r6), st .r3 60]

/-- The public modulus shape check precedes all Montgomery preparation. -/
def head (body : Prog isa) : Prog isa :=
  .seq (.block (prepareArgs 24 ++ domainPointers))
    (.seq (.block modulusCheck) (.ite .eq body (ret 0)))

def finishFlag : Prog isa := .block [.mov .r0 (.reg .r11)]

namespace CheckPublic

def entry : List Instr := [
  .addSp .r12 0, st .r0 24, st .r1 28, st .r2 32, st .r3 36,
  .ldrSp .r0 132, st .r0 0]

def main : Prog isa := .seq (prepareAt 24) (.seq (importAt 1 36 32)
  (.seq (inRange 1) (ifFlag (withQ (.seq (subgroup 36) finishFlag) (ret 1)) (ret 0))))

def code : Prog isa := framed (.seq (.block entry) (head main))
end CheckPublic

namespace CheckDomain

def entry : List Instr := [
  .addSp .r12 0, st .r0 24, st .r1 28, st .r2 32, .mov .r0 (.reg .r3), st .r0 0]

/-- Since q>2, checking p mod q=1 is equivalent to q dividing p-1.
RSA's encode/decode reduction accepts the full-width p as its input. -/
def divides : Prog isa := .seq (prepareAt 60) (.seq (importAt 1 24 32)
  (.seq (smallConst 7 1) (.seq (reduceOperand 1) (isOne 1))))

def qRange : Prog isa := .seq (importAt 1 60 32)
  (.seq (inRange 1) (.seq (.block saveFlag) (.seq (odd 1) (.block andFlag))))

def qChecks : Prog isa := .seq qRange (ifFlag
  (.seq divides (ifFlag (.seq (prepareAt 24) (.seq (subgroup 56) finishFlag)) (ret 0))) (ret 0))

def main : Prog isa := .seq (prepareAt 24) (.seq (importAt 1 56 32)
  (.seq (inRange 1) (ifFlag (withQ qChecks (ret 1)) (ret 0))))

def code : Prog isa := framed (.seq (.block entry) (head main))
end CheckDomain

namespace Exchange

def entry : List Instr := [
  .addSp .r12 0, st .r0 4, st .r2 24, st .r3 28,
  .ldrSp .r3 128, st .r3 32, .ldrSp .r3 132, st .r3 40,
  .ldrSp .r3 136, st .r3 44, .ldrSp .r3 140, st .r3 36,
  .ldrSp .r0 148, st .r0 0]

def saveResult : List Instr := [.addSp .r12 0, st .r11 64]

def exportResult : Prog isa := .seq (.block [
  .mov .r2 (.imm 6), .ldrSp .r4 4, .ldrSp .r6 32]) exportBE

/-- Mask every output byte with the returned validity flag. -/
def maskOutput : Prog isa := .seq (.block [
  .ldrSp .r0 4, .ldrSp .lr 32, .ldrSp .r2 64,
  .mov .r3 (.imm 0), .dp .sub .r2 .r3 (.reg .r2)])
  (.seq maskBytes (.block [.ldrSp .r0 64]))

def main : Prog isa := .seq (prepareAt 24) (.seq (powerAt 36 40 44)
  (.seq (inRange 6) (.seq (.block saveResult) (.seq exportResult maskOutput))))

def code : Prog isa := framed (.seq (.block entry) (head main))
end Exchange

namespace CheckPrivate

def entry : List Instr := [
  .addSp .r12 0, st .r0 24, st .r1 28, st .r2 32, st .r3 36,
  .ldrSp .r3 132, st .r3 40, .ldrSp .r3 136, st .r3 44,
  .ldrSp .r0 140, st .r0 0]

/-- Scalar comparisons use every word; only the final status branches. -/
def scalarRange : Prog isa := .seq (nonzero 1) (.seq (.block saveFlag)
  (.seq (withQ (.seq (importAt 6 60 32) (arrayCompare 1 6)) (belowP 1)) (.block andFlag)))

def matchPublic : Prog isa := .seq (powerAt 56 40 44)
  (.seq (importAt 1 36 32) (.seq (equal 6 1) finishFlag))

def tail : Prog isa := withQ
  (.seq (subgroup 36) (ifFlag matchPublic (ret 0))) matchPublic

def publicCheck : Prog isa := .seq (importAt 1 36 32)
  (.seq (inRange 1) (ifFlag tail (ret 0)))

def main : Prog isa := .seq (prepareAt 24) (.seq (importAt 1 40 44)
  (.seq scalarRange (ifFlag publicCheck (ret 2))))

def code : Prog isa := framed (.seq (.block entry) (head main))
end CheckPrivate

end VG.Impl.Ffdh.Arm.Domain
