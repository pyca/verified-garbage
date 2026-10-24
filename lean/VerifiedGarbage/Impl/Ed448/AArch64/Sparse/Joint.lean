module

public import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Table
public import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Recode

/-! Public joint sparse multiplication, with eight-bit base digits and
five-bit public-key digits. The input scalars are used without reduction. -/

@[expose] public section

namespace VG.Impl.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.Ed448.AArch64
open VG.Impl.X448.AArch64 (slot ld st BITS)
open VG.Impl.X448.AArch64.Base (constSlot)

/-- The scalar value's sign in x21 and its positive magnitude in x11. -/
def magnitude : List Instr :=
  [.lsr .x .x21 .x11 7, .movz .x .x9 256 0, .sub .x .x9 .x9 .x11,
   .movz .x .x8 128 0, .tst .x .x11 .x8, .cselc .x .x11 .x9 .x11 .ne]

def negateSelected : Prog isa :=
  X448.AArch64.Fast.opsK [.sub (slot 6) (slot 19) (slot 6)]

/-- Affine addition in place, reusing the existing interleaved point formula.
The saved GPRs occupy unused bytes beyond the runtime table and digit arrays. -/
def addAffine : Prog isa :=
  .seq (.block ((List.range 8).map (fun i => st (X448.AArch64.Fast.saved i) (7360+8*i)) ++
    [.movz .x .x12 0xffff 0, .movk .x .x12 0x0fff 1] ++
    X448.AArch64.Base.addAffine (slot 3) (slot 4) (slot 5) (slot 6) (slot 7)))
  (.block ((List.range 8).map fun i => ld (X448.AArch64.Fast.saved i) (7360+8*i)))

/-- Read a signature digit through an encodable pointer offset. -/
def baseDigit : List Instr :=
  [.add .x .x2 .x3 .x19, .addImm .x .x2 .x2 3400, .addImm .x .x2 .x2 3400,
   .ldrb .x11 .x2 0]

def keyDigit : List Instr := [.add .x .x2 .x3 .x19, .ldrb .x11 .x2 BITS]

def addBase : Prog isa :=
  .seq (.block baseDigit) <|
  .ite (.nonzero .x .x11)
    (.seq (.block magnitude) <| .seq (.block selectBase) <|
      .seq (.ite (.nonzero .x .x21) negateSelected (.block [])) addAffine)
    (.block [])

def addKey : Prog isa :=
  .seq (.block keyDigit) <|
  .ite (.nonzero .x .x11)
    (.seq (.block magnitude) <| .seq (.block selectKey) <|
      .seq (.ite (.nonzero .x .x21) negateSelected (.block [])) Point56.addCall)
    (.block [])

def step : Prog isa :=
  .seq (.block [.subImm .x .x19 .x19 1]) <| .seq Point56.doubleCall <|
  .seq addBase <| .seq addKey (.block [.addImm .x .x9 .x19 0])

def init : List Instr :=
  constSlot (slot 3) 0 ++ constSlot (slot 4) 1 ++ constSlot (slot 5) 1 ++
  constSlot (slot 19) 0 ++ constSlot (slot 20) 1 ++ [.movz .x .x19 464 0]

/-- Scan leading zero digits of both public scalars. Index zero ends the scan
also for the all-zero pair; the main loop then performs one neutral step. -/
def trimStep : List Instr :=
  [.subImm .x .x19 .x19 1] ++ baseDigit ++
  [.addImm .x .x7 .x11 0] ++ keyDigit ++
  [.logic .orr .x .x9 .x7 .x11, .subImm .x .x4 .x19 1,
   .lsr .x .x4 .x4 63, .logic .orr .x .x9 .x9 .x4]

/-- The joint loop once both complete signed digit streams are available. -/
def jointDigits : Prog isa :=
  .seq (.block init) <| .seq (.loop (.block trimStep) (.zero .x .x9)) <|
  .seq (.block [.addImm .x .x19 .x19 1]) (.loop step (.nonzero .x .x9))

def recodePair : Prog isa :=
  .seq (recodeBits true) <| .seq (.block copySignatureDigits) <|
  .seq (bitsAt .x3 KB 0 BITS) (recodeBits false)

def joint : Prog isa := .seq recodePair jointDigits

end VG.Impl.Ed448.AArch64.Sparse
