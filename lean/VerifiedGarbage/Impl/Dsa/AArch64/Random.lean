module

public import VerifiedGarbage.Impl.Dsa.AArch64.Checks

/-! Bounded rejection sampling from a random tape on AArch64. -/
@[expose] public section
namespace VG.Impl.Dsa.AArch64.Random
open VG VG.AArch64 VG.Impl.Bignum.AArch64

def oOut : Nat := 40
def oOutLen : Nat := 48
def oUsedPtr : Nat := 56
def oKey : Nat := 64
def oKeyLen : Nat := 72
def oPLen : Nat := 80
def oQLen : Nat := 88
def oDigest : Nat := 96
def oDigestLen : Nat := 104
def oRand : Nat := 112
def oRandLen : Nat := 120
def oScratch : Nat := 128
def oScratchLen : Nat := 136
def oUsed : Nat := 144
def oAttempts : Nat := 152
def oDraws : Nat := 160
def oQ : Nat := 168
def oWidth : Nat := 176
def oMask : Nat := 184
def oStatus : Nat := 192
def oNonce : Nat := 200
def frameBytes : Nat := 256

/-- Stores use a caller-saved address register. -/
def store (offset : Nat) (r : Reg) : List Instr :=
  [.addSp .x15 offset, .str .x r .x15 0]

def address (r : Reg) (offset : Nat) : List Instr := [.addSp r offset]

def copySlot (src dst : Nat) : List Instr := [.ldrSp .x0 src] ++ store dst .x0

def significant : Prog isa :=
  .seq (.block [mov .x1 .x12, mov .x13 .x9])
    (.seq Checks.significant
      (.block [.sub .x .x13 .x13 .x8, .add .x .x12 .x12 .x13,
        mov .x9 .x8, mov .x0 .x10]))

def maskStep (threshold bits : Nat) : List Instr :=
  [movi .x4 bits, movi .x3 threshold, .subs .x .x3 .x0 .x3,
    .csel .x .x8 .x8 .x4]

def maskCode : List Instr :=
  [movi .x8 255] ++ maskStep 128 127 ++ maskStep 64 63 ++ maskStep 32 31 ++
    maskStep 16 15 ++ maskStep 8 7 ++ maskStep 4 3 ++ maskStep 2 1

def mask : Prog isa := .block maskCode

def clearNonce : List Instr :=
  [movi .x0 0] ++ store oNonce .x0 ++ store (oNonce + 8) .x0 ++
    store (oNonce + 16) .x0 ++ store (oNonce + 24) .x0

def prepareFinish : Prog isa :=
  .seq (.block [mov .x10 .x0])
    (.seq mask (.block (store oMask .x8 ++
      [movi .x0 0, movi .x4 1, movi .x3 2, .subs .x .x3 .x9 .x3,
       .csel .x .x0 .x4 .x0, movi .x3 2, .subs .x .x3 .x10 .x3,
       .csel .x .x0 .x4 .x0])))

def prepare : Prog isa :=
  .seq (.block (clearNonce ++ [.ldrSp .x12 oQ, .ldrSp .x9 oQLen]))
    (.seq significant (.seq (.block (store oQ .x12 ++ store oWidth .x9)) prepareFinish))

def copyByte : List Instr :=
  [.ldrb .x0 .x12 0, .strb .x0 .x2 0, .addImm .x .x12 .x12 1,
    .addImm .x .x2 .x2 1, .subImm .x .x9 .x9 1]

def copyHeader : List Instr :=
  [.ldrSp .x12 oRand, .ldrSp .x4 oUsed, .add .x .x12 .x12 .x4,
    .ldrSp .x9 oWidth, .addSp .x2 oNonce, .ldrSp .x4 oQLen,
    .add .x .x2 .x2 .x4, .sub .x .x2 .x2 .x9]

def copyFirst : List Instr :=
  [.ldrb .x0 .x12 0, .ldrSp .x4 oMask, .logic .and .x .x0 .x0 .x4,
    .strb .x0 .x2 0, .addImm .x .x12 .x12 1,
    .addImm .x .x2 .x2 1, .subImm .x .x9 .x9 1]

def copyInit : List Instr := copyHeader ++ copyFirst

def copyRest : Prog isa :=
  .ite (.nonzero .x .x9) (.loop (.block copyByte) (.nonzero .x .x9)) (.block [])

def copy : Prog isa := .seq (.block copyInit) copyRest

def borrow : List Instr :=
  [.add .x .x4 .x4 .x8, .sub .x .x0 .x0 .x4, .lsr .x .x0 .x0 63, mov .x8 .x0]

def rangeByte : List Instr :=
  [.subImm .x .x2 .x2 1, .subImm .x .x12 .x12 1,
    .ldrb .x0 .x2 0, .logic .orr .x .x10 .x10 .x0, .ldrb .x4 .x12 0] ++
    borrow ++ [.subImm .x .x9 .x9 1]

def rangeFinish : List Instr :=
  [movi .x0 0, .tst .x .x10 .x10, .cselc .x .x8 .x0 .x8 .eq]

def rangeInit : List Instr :=
  [.addSp .x2 oNonce, .ldrSp .x4 oQLen, .add .x .x2 .x2 .x4,
    .ldrSp .x12 oQ, .ldrSp .x9 oWidth, .add .x .x12 .x12 .x9,
    movi .x8 0, movi .x10 0]

def inRange : Prog isa :=
  .seq (.block rangeInit)
    (.seq (.loop (.block rangeByte) (.nonzero .x .x9)) (.block rangeFinish))

def drawFinish : Prog isa :=
  .ite (.nonzero .x .x8) (.block ([movi .x0 1] ++ store oStatus .x0))
    (.seq (.block ([.ldrSp .x0 oDraws, .subImm .x .x0 .x0 1] ++ store oDraws .x0))
      (.ite (.zero .x .x0) (.block (store oStatus .x0)) (.block [])))

def draw : Prog isa :=
  .seq (.block [.ldrSp .x0 oRandLen, .ldrSp .x4 oUsed, .sub .x .x0 .x0 .x4,
      .ldrSp .x4 oWidth, .subs .x .x3 .x0 .x4, movi .x0 0, movi .x4 1,
      .csel .x .x3 .x0 .x4])
    (.ite (.nonzero .x .x3) (.block ([movi .x0 2] ++ store oStatus .x0))
      (.seq copy
        (.seq (.block ([.ldrSp .x0 oUsed, .ldrSp .x4 oWidth, .add .x .x0 .x0 .x4] ++
            store oUsed .x0)) (.seq inRange drawFinish))))

def statusTest (n : Nat) : List Instr :=
  [.ldrSp .x0 oStatus, .subImm .x .x4 .x0 n]

def sample : Prog isa :=
  .seq (.block ([movi .x0 128] ++ store oDraws .x0 ++ [movi .x0 4] ++ store oStatus .x0))
    (.seq (.loop (.seq draw (.block (statusTest 4))) (.zero .x .x4))
      (.block [.ldrSp .x0 oStatus]))

end VG.Impl.Dsa.AArch64.Random
