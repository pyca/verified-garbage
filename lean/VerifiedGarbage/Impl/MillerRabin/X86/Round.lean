module

public import VerifiedGarbage.Impl.MillerRabin.X86.Ops
public import VerifiedGarbage.Impl.Mont.X86.Compact

/-! # Prepared fixed-window Miller–Rabin on i686

The modulus, inverse and Montgomery constants are prepared once by the
candidate path. Each round builds its sixteen powers with fourteen
products, writes each table entry once, and scans the whole table for every
secret four-bit digit. The product loop is the paired-word CIOS multiplier.
Neither the exponent, witness, comparison results nor digit affect an
address or branch. Three final squarings use the prepared exponent marker.
-/

@[expose] public section
namespace VG.Impl.MillerRabin.X86
open VG VG.X86

/-- The caller's frame has four saved registers. Read ws_len before pushing
Montgomery's five cdecl arguments; its 16-byte frame fits below those. -/
def mulY (montName : String) (montCode : Prog isa) (b : Nat) : Prog isa :=
  .seq (.block [.mov .eax (.imm (BitVec.ofNat 32 b)), .mov .ecx (.imm 6),
    .mov .edx (.mem (at_ .esp 24))])
    (.frame (.push [.eax, .ecx, .ecx, .edx, .edi]) (.call montName montCode) (.pop .eax 5))

/-- The table is built in place, with one copy per completed power. -/
def table (montName : String) (montCode : Prog isa) : Prog isa :=
  seqs ([copy aTable aOne, copy (aTable + 1) aX, copy aY aX] ++
    (List.range 14).map fun j => .seq (mulY montName montCode aX) (copy (aTable + j + 2) aY))

/-- Add y=-1 to the flag when the secret threshold is below the public
square counter; the final counter subtraction alone controls the loop. -/
def squareFlag : List Instr :=
  [.mov .eax (.mem (slot sSquares)), .mov .edx (.mem (slot sThreshold)),
    .alu .sub .edx (.reg .eax), .shift .shr .edx 31, .mov .ecx (.mem (slot sEq2)),
    .alu .and .ecx (.reg .edx), .mov .edx (.mem (slot sFlag)), .alu .or .edx (.reg .ecx),
    .store (slot sFlag) .edx, .alu .sub .eax (.imm 1), .store (slot sSquares) .eax]

def squareStep (montName : String) (montCode : Prog isa) : Prog isa :=
  seqs [mulY montName montCode aY, equal sEq2 aY aMinusOne, .block squareFlag]

def squareLoop (montName : String) (montCode : Prog isa) : Prog isa :=
  .loop (squareStep montName montCode) .ne

def fourSquares : List Instr :=
  [.mov .eax (.imm 0), .store (slot sThreshold) .eax, .mov .eax (.imm 4), .store (slot sSquares) .eax]

/-- A nonzero digit replaces the flag by y=1 or y=-1. For a zero digit the
flag from the squarings is kept. The exponent word advances by four bits. -/
def windowEnd : List Instr :=
  [.mov .eax (.mem (slot sValue)), .mov .edx (.reg .eax), .shift .shr .edx 28,
    .alu .sub .edx (.imm 1), .shift .shr .edx 31, .mov .ebx (.reg .edx), .alu .xor .ebx (.imm 1),
    .mov .ecx (.mem (slot sEq1)), .alu .or .ecx (.mem (slot sEq2)), .alu .and .ecx (.reg .ebx),
    .alu .and .edx (.mem (slot sFlag)), .alu .or .ecx (.reg .edx), .store (slot sFlag) .ecx,
    .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax),
    .store (slot sValue) .eax, .mov .eax (.mem (slot sWindows)), .alu .sub .eax (.imm 1),
    .store (slot sWindows) .eax]

def window (montName : String) (montCode : Prog isa) : Prog isa :=
  seqs [.block fourSquares, squareLoop montName montCode, scan, mulY montName montCode aX,
    equal sEq1 aY aOne, equal sEq2 aY aMinusOne, .block windowEnd]

/-- One exponent word, with its eight windows read from most significant to
least significant. The native word index is public. -/
def loadWord : List Instr :=
  ptr .ebp aExponent ++ [.mov .eax (.mem (slot sWords)), .alu .sub .eax (.imm 1),
    .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .alu .add .ebp (.reg .eax),
    .mov .eax (.mem (at_ .ebp 0)), .store (slot sValue) .eax,
    .mov .eax (.imm 8), .store (slot sWindows) .eax]

def wordEnd : List Instr :=
  [.mov .eax (.mem (slot sWords)), .alu .sub .eax (.imm 1), .store (slot sWords) .eax]

def wordStep (montName : String) (montCode : Prog isa) : Prog isa :=
  seqs [.block loadWord, .loop (window montName montCode) .ne, .block wordEnd]

def initWindows : List Instr :=
  words ++ [.store (slot sWords) .esi, .mov .eax (.imm 0), .store (slot sFlag) .eax]

/-- Fold the 64-bit power-of-two marker to four bits and derive 4-sigma.
No branch depends on that marker or on the number of active final squares. -/
def lastSquares : List Instr :=
  ptr .ebp aExponent ++ words ++ [.mov .eax (.reg .esi), .alu .add .eax (.reg .eax),
    .alu .add .eax (.reg .eax), .alu .add .ebp (.reg .eax), .mov .eax (.mem (at_ .ebp 0)),
    .alu .or .eax (.mem (at_ .ebp 4)),
    .mov .edx (.reg .eax), .shift .shr .edx 16, .alu .or .eax (.reg .edx),
    .mov .edx (.reg .eax), .shift .shr .edx 8, .alu .or .eax (.reg .edx),
    .mov .edx (.reg .eax), .shift .shr .edx 4, .alu .or .eax (.reg .edx),
    .mov .edx (.reg .eax), .shift .shr .edx 1, .alu .and .edx (.imm 1),
    .mov .ebx (.reg .eax), .shift .shr .ebx 2, .alu .and .ebx (.imm 1),
    .shift .shr .eax 3, .alu .and .eax (.imm 1),
    .alu .add .eax (.reg .edx), .alu .add .eax (.reg .edx), .alu .add .eax (.reg .edx),
    .alu .add .eax (.reg .ebx), .alu .add .eax (.reg .ebx), .store (slot sThreshold) .eax,
    .mov .eax (.imm 3), .store (slot sSquares) .eax]

def body (montName : String) (montCode : Prog isa) : Prog isa :=
  seqs [.block [.mov .edi (.mem (at_ .esp 20))], table montName montCode, copy aY aOne,
    .block initWindows, .loop (wordStep montName montCode) .ne, .block lastSquares,
    squareLoop montName montCode, .block [.mov .eax (.mem (slot sFlag))]]

def code (montName : String) (montCode : Prog isa) : Prog isa :=
  .frame (.push [.ebx, .ebp, .esi, .edi])
    (.seq (body montName montCode) (.block VG.Impl.Mont.X86.Compact.restoreRegs)) (.pop .ebx 4)

end VG.Impl.MillerRabin.X86
