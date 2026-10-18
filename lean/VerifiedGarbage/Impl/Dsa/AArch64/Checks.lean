module

public import VerifiedGarbage.Impl.Dsa.AArch64.Core

/-! # DSA public-width scans and acceptance masks -/

@[expose] public section

namespace VG.Impl.Dsa.AArch64.Checks
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Dsa.Layout

def accumulate : List Instr :=
  [Core.field .x4 .mask, .logic .and .x .x3 .x3 .x4, .str .x .x3 .x0 Field.mask.offset]

def significantChoose : Prog isa :=
  .ite (.zero .x .x8)
    (.ite (.nonzero .x .x3) (.block [mov .x8 .x9, mov .x10 .x3]) (.block []))
    (.block [])

def significantByte : Prog isa := seqs [
  .block [.ldrb .x3 .x1 0], significantChoose,
  .block [.addImm .x .x1 .x1 1, .subImm .x .x9 .x9 1]]

def significant : Prog isa := seqs [
  .block [movi .x8 0, movi .x10 0], .loop significantByte (.nonzero .x .x9)]

def zeroMask (r : Reg) (invert : Bool := false) : List Instr :=
  [.tst .x r r, movi .x3 0, .subImm .x .x4 .x3 1,
    .cselc .x .x3 .x4 .x3 (if invert then .ne else .eq)]

def widthMask (n : Nat) : List Instr :=
  ([movi .x3 n, .logic .eor .x .x3 .x8 .x3] : List Instr) ++ zeroMask .x3

/-- All imported subgroup widths for a 2048-bit modulus, including legacy 160-bit q. -/
def width2048 : List Instr :=
  widthMask 28 ++ ([mov .x11 .x3] : List Instr) ++ widthMask 32 ++
    ([.logic .orr .x .x3 .x3 .x11] : List Instr) ++ ([mov .x11 .x3] : List Instr) ++ widthMask 20 ++
    ([.logic .orr .x .x3 .x3 .x11] : List Instr)

def topMask : List Instr :=
  [.lsr .x .x3 .x10 7, movi .x4 0, .sub .x .x3 .x4 .x3]

def shapeP : List Instr :=
  ([sth .x8 22] : List Instr) ++ Checks.topMask ++ [.str .x .x3 .x0 Field.mask.offset]

def shapeQ : List Instr :=
  ([.str .x .x8 .x0 Field.digestPrefixLen.offset] : List Instr) ++ Checks.topMask ++ Checks.accumulate

def widthChoice : Prog isa :=
  .ite (.zero .x .x6) (.block (Checks.widthMask 20))
    (.seq (.block [.subImm .x .x6 .x2 256])
      (.ite (.zero .x .x6)
        (.block width2048)
        (.seq (.block [.subImm .x .x6 .x2 384])
          (.ite (.zero .x .x6) (.block (Checks.widthMask 32)) (.block [movi .x3 0])))))

def shapeSizes : Prog isa := seqs [
  .block [Core.field .x1 .p, Core.field .x9 .pLen],
  Checks.significant,
  .block (shapeP ++ ([Core.field .x1 .q, Core.field .x9 .qLen] : List Instr)),
  Checks.significant,
  .block (shapeQ ++ ([ldh .x2 22, .subImm .x .x6 .x2 128] : List Instr)),
  widthChoice]

def oddCombine : List Instr :=
  [.logic .and .x .x3 .x3 .x2, movi .x2 1, .logic .and .x .x3 .x3 .x2,
    movi .x2 0, .sub .x .x3 .x2 .x3]

def oddCheck : List Instr :=
  ([Core.field .x1 .p, Core.field .x9 .pLen, .subImm .x .x9 .x9 1,
    .add .x .x1 .x1 .x9, .ldrb .x3 .x1 0] : List Instr) ++
  ([Core.field .x1 .q, Core.field .x9 .qLen, .subImm .x .x9 .x9 1,
    .add .x .x1 .x1 .x9, .ldrb .x2 .x1 0] : List Instr) ++ oddCombine ++ Checks.accumulate

def shapeFinish : List Instr :=
  [Core.field .x3 .digestLen, Core.field .x2 .digestPrefixLen,
    .subs .x .x4 .x2 .x3, .csel .x .x3 .x3 .x2,
    .str .x .x3 .x0 Field.digestPrefixLen.offset, Core.field .x3 .mask]

def shapeTail : List Instr := Checks.accumulate ++ oddCheck ++ shapeFinish

def domainShape : Prog isa := .seq shapeSizes (.block shapeTail)

def zeroByte : List Instr := [.ldrb .x3 .x1 0, .logic .orr .x .x8 .x8 .x3,
  .addImm .x .x1 .x1 1, .subImm .x .x9 .x9 1]

def zero (a : Operand) (nonzero : Bool := false) : Prog isa := seqs [
  .block (Core.pointer a.pointer ++ ([mov .x1 .x3, Core.field .x9 a.length, movi .x8 0] : List Instr)),
  .loop (.block zeroByte) (.nonzero .x .x9), .block (zeroMask .x8 nonzero ++ accumulate)]

def equalByte : List Instr := [.ldrb .x3 .x1 0, .ldrb .x10 .x2 0,
  .logic .eor .x .x3 .x3 .x10, .logic .orr .x .x8 .x8 .x3,
  .addImm .x .x1 .x1 1, .addImm .x .x2 .x2 1, .subImm .x .x9 .x9 1]

def equal (a b : Operand) (unequal : Bool := false) : Prog isa := seqs [
  .block (Core.pointer a.pointer ++ ([mov .x1 .x3] : List Instr) ++ Core.pointer b.pointer ++
    ([mov .x2 .x3, Core.field .x9 a.length, movi .x8 0] : List Instr)),
  .loop (.block equalByte) (.nonzero .x .x9), .block (zeroMask .x8 unequal ++ accumulate)]

def lowerScan (aboveOne : Bool) : Prog isa := seqs [
  .block [ldh .x12 sW, ldh .x16 (sArr aX)],
  .block (([ld .x15 .x16] : List Instr) ++ (if aboveOne then [.lsr .x .x15 .x15 1] else [])),
  .block [next .x16, .subImm .x .x14 .x12 1],
  countLoop .x14 [ld .x3 .x16, .logic .orr .x .x15 .x15 .x3, next .x16]]

def rangeMask (aboveOne : Bool) : Prog isa := seqs [
  lowerScan aboveOne,
  .block [ldh .x16 (sArr aX), ldh .x17 (sArr aN), ldh .x14 sW, movi .x7 0, .subs .x .x3 .x7 .x7],
  cmpLoop,
  .block [movi .x3 0, .subImm .x .x4 .x3 1, .csel .x .x5 .x3 .x4],
  .block (zeroMask .x15 true ++ [.logic .and .x .x3 .x3 .x5])]

def range (ws : Nat) (a : Operand) (aboveOne : Bool := false) : Prog isa := seqs [
  .block (Core.operand arg argLen a ++ Core.enter ws), Arithmetic.load aX arg argLen,
  rangeMask aboveOne, .block (([Crt.leave] : List Instr) ++ accumulate)]

def oneScan : Prog isa := seqs [
  .block [ldh .x12 sW, ldh .x16 (sArr aX)],
  .block [ld .x15 .x16, movi .x3 1, .logic .eor .x .x15 .x15 .x3],
  .block [next .x16, .subImm .x .x14 .x12 1],
  countLoop .x14 [ld .x3 .x16, .logic .orr .x .x15 .x15 .x3, next .x16]]

def isOne (ws : Nat) (a : Operand) : Prog isa :=
  .seq (.block (Core.operand arg argLen a ++ Core.enter ws))
    (.seq (.seq (Arithmetic.load aX arg argLen) (.seq oneScan (.block (zeroMask .x15))))
      (.block (([Crt.leave] : List Instr) ++ accumulate)))

def minusHead (amount : Nat) : List Instr :=
  [ldh .x14 sW, ldh .x16 (sArr aN), ldh .x17 (sArr aY), movi .x4 amount,
    movi .x7 0, ld .x3 .x16, .subs .x .x3 .x3 .x4, st .x3 .x17,
    next .x16, next .x17, .subImm .x .x14 .x14 1]

def minusTail : List Instr :=
  [ld .x3 .x16, .sbcs .x .x3 .x3 .x7, st .x3 .x17, next .x16, next .x17]

def modulusMinus (ws amount : Nat) (output : Operand) : Prog isa :=
  .seq (.block (Core.operand result resultLen output ++ Core.enter ws))
    (.seq (.seq (.block (minusHead amount)) (countLoop .x14 minusTail)) (seqs Core.finish))

/-- Range and domain checks before the public subgroup exponentiations. -/
def publicPrefix (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) := [
  range pWorkspace Core.generator true, range pWorkspace Core.publicValue true,
  modulusMinus pWorkspace 1 (Core.element t),
  Core.reduce mul (Core.element t) (Core.scalar u), zero (Core.scalar u),
  modulusMinus qWorkspace 2 (Core.scalar qMinusTwo)]

/-- Signing also checks `g^x = y`, so `g^q = 1` implies the public value's subgroup check. -/
def signingKey (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs (publicPrefix mul ++ [
  Core.publicPow mul pWorkspace Core.generator ⟨.input .q, .qLen⟩ (Core.element t),
  isOne pWorkspace (Core.element t)])

/-- Check both subgroup memberships independently, with public q windows. -/
def publicKey (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs (publicPrefix mul ++ [
  Core.publicPow mul pWorkspace Core.generator ⟨.input .q, .qLen⟩ (Core.element t),
  isOne pWorkspace (Core.element t),
  Core.publicPow mul pWorkspace Core.publicValue ⟨.input .q, .qLen⟩ (Core.element t),
  isOne pWorkspace (Core.element t)])

/-- Private/public key consistency and nonce rejection masks. -/
def privateKey (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
  range qWorkspace Core.privateScalar, range qWorkspace Core.nonce,
  Core.pow mul pWorkspace Core.generator Core.privateScalar (Core.element t),
  equal (Core.element t) Core.publicValue]

end VG.Impl.Dsa.AArch64.Checks
