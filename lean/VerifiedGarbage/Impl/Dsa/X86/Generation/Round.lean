module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Square
public import VerifiedGarbage.Impl.Dsa.X86.Checks

/-! # A public-input Miller–Rabin round using a prepared modulus

The exponentiation leaves its ordinary result in slot six. The round
compares it against one (slot three) and modulus minus one (slot eight).
The remaining squaring count and final result live beyond the largest
Montgomery context. Zero means composite, one means the round passed.
-/
@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86

def roundCount : Nat := 8260
def roundStatus : Nat := 8264

def roundMinusOne (n : Nat) : Prog isa :=
  chainW .sbb (2 * n) (slot n 8) (slot n 0) (slot n 3)

def roundCompare (n : Nat) : Prog isa :=
  .seq (equal n (slot n 6) (slot n 8))
    (.seq (.block [.store (sc roundStatus) .edx])
      (.seq (equal n (slot n 6) (slot n 3))
        (.block [.alu .or .edx (.mem (sc roundStatus)), .alu .cmp .edx (.imm 0)])))

/-- After a square, only minus one makes the round succeed. Equality with
one still terminates the loop, with the stored status zero. -/
def roundSquare (n : Nat) : Prog isa :=
  .seq (ordinarySquare n) (roundCompare n)

def roundStop : List Instr := [.mov .eax (.imm 0), .alu .cmp .eax (.imm 0)]

def roundNext : List Instr :=
  [.mov .eax (.mem (sc roundCount)), .alu .sub .eax (.imm 1),
   .store (sc roundCount) .eax, .alu .cmp .eax (.imm 0)]

/-- When neither terminal value occurs, decrement the remaining count.
A nonzero comparison terminates without consuming another square. -/
def roundStep (n : Nat) : Prog isa :=
  .seq (roundSquare n) (.ite .ne (.block roundStop) (.block roundNext))

def roundAccept : List Instr := [.mov .eax (.imm 1), .store (sc roundStatus) .eax]
def roundCountTest : List Instr := [.mov .eax (.mem (sc roundCount)), .alu .cmp .eax (.imm 0)]
def roundResult : List Instr := [.mov .eax (.mem (sc roundStatus)), .alu .and .eax (.imm 1)]

def roundTests (n : Nat) : Prog isa :=
  .seq (roundCompare n)
    (.seq (.ite .ne (.block roundAccept)
      (.seq (.block roundCountTest) (.ite .e (.block []) (.loop (roundStep n) .ne))))
      (.block roundResult))

/-- The caller sets `roundCount` to `a - 1`, with `1 ≤ a`, and performs
exponentiation using the candidate's odd part before this operation. -/
def roundFinish (n : Nat) : Prog isa := .seq (roundMinusOne n) (roundTests n)

/-- Reuse the candidate's Montgomery context across witnesses. -/
def round (n expWords : Nat) : Prog isa :=
  .seq (exponentiate n expWords) (roundFinish n)
end VG.Impl.Dsa.X86.Generation
