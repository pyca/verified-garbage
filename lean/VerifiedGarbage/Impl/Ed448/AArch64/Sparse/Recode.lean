module

import VerifiedGarbage.Impl.Ed448.AArch64.VerifyWindow
public import VerifiedGarbage.Impl.Ed448.WnafWide
public import VerifiedGarbage.Impl.X448.AArch64.Common
public import VerifiedGarbage.Impl.X448.AArch64.Fast
public import VerifiedGarbage.Spec.Ed448
public import VerifiedGarbage.TCB.Artifact

/-! Public scalar recoding into signed byte digits, within the existing workspace.
The 456 original positions run in place over expanded bits. Eight tail
positions have zero input and never read past the padded bit string. -/

@[expose] public section

namespace VG.Impl.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.X448.AArch64 (BITS)

/-- Saved signature digits; the live challenge digits remain at BITS. -/
def SDIG : Nat := 6800

def width (wide : Bool) : Nat := if wide then 8 else 5

def digitStep (wide : Bool) : List Instr :=
  let h := WnafWide.half wide
  let b := WnafWide.radix wide
  [.add .x .x4 .x4 .x6, .addImm .x .x4 .x4 h, .movz .x .x8 (BitVec.ofNat 16 (b-1)) 0,
   .logic .and .x .x4 .x4 .x8, .subImm .x .x7 .x4 b,
   .movz .x .x8 (BitVec.ofNat 16 h) 0, .tst .x .x4 .x8, .cselc .x .x7 .x4 .x7 .eq,
   .movz .x .x8 1 0, .tst .x .x4 .x8, .movz .x .x9 0 0, .cselc .x .x7 .x9 .x7 .eq,
   .add .x .x6 .x6 .x5, .addImm .x .x6 .x6 h, .sub .x .x6 .x6 .x7, .lsr .x .x6 .x6 1]

/-- The current expanded bit and the next w-1 bits, high bit first. -/
def loadBits (wide : Bool) : List Instr :=
  [.add .x .x2 .x3 .x19, .ldrb .x4 .x2 (BITS+width wide-1)] ++
  (List.range (width wide-1)).reverse.flatMap fun i =>
    [.ldrb .x5 .x2 (BITS+i), .lsl .x .x4 .x4 1, .add .x .x4 .x4 .x5]

def writeDigit : List Instr :=
  [.strb .x7 .x2 BITS, .addImm .x .x19 .x19 1]

def recodeBody (wide : Bool) : List Instr :=
  loadBits wide ++ digitStep wide ++ writeDigit ++ [.subImm .x .x9 .x19 456]

/-- A carry position: zero lookahead, with the current destination pointer. -/
def zeroStep (wide : Bool) : List Instr :=
  [.add .x .x2 .x3 .x19, .movz .x .x4 0 0, .movz .x .x5 0 0] ++ digitStep wide ++ writeDigit

def recodeTail (wide : Bool) : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (.block (zeroStep wide)) (recodeTail wide n)

/-- Clear all eight lookahead padding bytes in one aligned store. -/
def recodeInit (wide : Bool) : List Instr :=
  [.movz .x .x4 0 0,.str .x .x4 .x3 (BITS+456),.movz .x .x19 0 0,
   .movz .x .x6 (BitVec.ofNat 16 (WnafWide.half wide)) 0]

def recodeBits (wide : Bool) : Prog isa :=
  .seq (.block (recodeInit wide)) <|
  .seq (.loop (.block (recodeBody wide)) (.nonzero .x .x9)) (recodeTail wide 8)

/-- Copy signed S digits out before expanding the challenge over BITS. -/
def copySignatureDigits : List Instr :=
  [.addImm .x .x10 .x3 3400, .addImm .x .x10 .x10 3400] ++
  (List.range 464).flatMap fun i => [.ldrb .x4 .x3 (BITS+i), .strb .x4 .x10 i]

end VG.Impl.Ed448.AArch64.Sparse
