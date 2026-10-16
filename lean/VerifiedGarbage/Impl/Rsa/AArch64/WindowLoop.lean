module

public import VerifiedGarbage.Impl.Rsa.AArch64.WindowTail

/-! Public length control for batches and trailing bytes. -/

@[expose] public section
namespace VG.Impl.Rsa.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64

def haveFive : List Instr :=
  [ldh .x3 Crt.sExpLen, ldh .x4 Crt.sI, .sub .x .x3 .x3 .x4, movi .x4 5,
    .subs .x .x3 .x3 .x4, movi .x4 1, movi .x5 0, .csel .x .x9 .x4 .x5]

def advance (n : Nat) : List Instr :=
  [ldh .x3 Crt.sI, .addImm .x .x3 .x3 n, sth .x3 Crt.sI]

def loadTailByte : List Instr :=
  [ldh .x3 Crt.sExp,ldh .x4 Crt.sI,.add .x .x3 .x3 .x4,.ldrb .x3 .x3 0,sth .x3 Crt.sV]

def remaining : List Instr :=
  [ldh .x3 Crt.sExpLen,ldh .x4 Crt.sI,.sub .x .x3 .x3 .x4]

def groupBody (window : Prog isa) : Prog isa :=
  .seq (appliedBatch window) (.block (advance 5 ++ haveFive))

def tailBody (window : Prog isa) : Prog isa :=
  .seq (.block loadTailByte) (.seq (tailBits window 8) (.block (advance 1 ++ remaining)))

def expGroups (window : Prog isa) : Prog isa :=
  .seq (.block haveFive)
    (.ite (.nonzero .x .x9) (.loop (groupBody window) (.nonzero .x .x9)) (.block []))

def expTail (window : Prog isa) : Prog isa :=
  .seq (.block remaining)
    (.ite (.nonzero .x .x3) (.loop (tailBody window) (.nonzero .x .x3)) (.block []))

def expInit (sp sl : Nat) : Prog isa :=
  .block [ldh .x5 Crt.sLink, VG.Impl.Rsa.AArch64.Crt.ldw .x3 .x5 sp, sth .x3 Crt.sExp,
    VG.Impl.Rsa.AArch64.Crt.ldw .x3 .x5 sl, sth .x3 Crt.sExpLen, movi .x3 0, sth .x3 Crt.sI]

def expHead (mul : Nat → Nat → Nat → Prog isa) (sp sl : Nat) : Prog isa :=
  .seq (expInit sp sl) (.seq (seqs (tabBuild32 mul)) (.block resetWindow))

/-- Complete the exponent from a prepared 32-entry table and zero pending bits. -/
def expRun (window : Prog isa) (mul : Nat → Nat → Nat → Prog isa) (select : Prog isa) : Prog isa :=
  .seq (expGroups window) (.seq (expTail window) (finish mul select))

def expLoop (window : Prog isa) (mul : Nat → Nat → Nat → Prog isa) (select : Prog isa)
    (sp sl : Nat) : Prog isa := .seq (expHead mul sp sl) (expRun window mul select)

open VG.Impl.Rsa.AArch64.Crt VG.Impl.Bignum.Public VG.Impl.Bignum.Crt in
/-- The q phase with the wider exponentiation table. -/
def qPhase (window : Prog isa) (mul : Nat → Nat → Nat → Prog isa) (select : Prog isa) : List (Prog isa) :=
  gPow mul sWsQ ++ [.block [enterQ]] ++ redc mul aY ++ copyArr aY aXc ++
  [.block [leave], mul aY aXm aY, .block [enterQ]] ++ redc mul aY ++
  [expLoop window mul select sDq sQlen, mul aY aY aOne, .block [leave]]

end VG.Impl.Rsa.AArch64.WindowFive
