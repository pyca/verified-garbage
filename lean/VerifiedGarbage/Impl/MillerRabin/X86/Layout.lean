module

public import VerifiedGarbage.TCB.X86.Isa

/-! # The compact prepared Miller–Rabin workspace on i686

EDI is the prepared Montgomery workspace base. Width and stride are read
from the existing header and retained across witnesses. Only the compact
contract's five scratch header words are used for flags and counters.
-/

@[expose] public section
namespace VG.Impl.MillerRabin.X86
open VG VG.X86

def at_ (r : Reg) (d : Nat) : MemOp := ⟨r, d⟩
def slot (d : Nat) : MemOp := at_ .edi d

def sEq1 : Nat := 8
def sEq2 : Nat := 12
def sFlag : Nat := 184
def sValue : Nat := 208
def sWords : Nat := 232
def sSquares : Nat := 236
def sWindows : Nat := 240
def sThreshold : Nat := 244

def aX : Nat := 5
def aY : Nat := 6
def aOne : Nat := 9
def aMinusOne : Nat := 10
def aTable : Nat := 11
def aExponent : Nat := 27

/-- A compile-time five-bit multiplication by an array index below 32.
Only additions execute; the index does not depend on candidate data. -/
def scaleIndex (r tmp : Reg) (j : Nat) : List Instr :=
  [4, 3, 2, 1, 0].flatMap fun bit =>
    [.alu .add r (.reg r)] ++ if j / 2 ^ bit % 2 = 1 then [.alu .add r (.reg tmp)] else []

/-- First-eight array pointers come from the prepared header. The remaining
arrays use its public stride, without extending or changing that header. -/
def ptr (r : Reg) (j : Nat) : List Instr :=
  if j < 8 then [.mov r (.mem (slot (64 + 8 * j)))] else
    [.mov .edx (.mem (slot 224)), .mov r (.imm 0)] ++ scaleIndex r .edx j ++
      [.alu .add r (.reg .edi), .alu .add r (.imm 256)]

/-- The number of native words is twice the prepared 64-bit width. -/
def words : List Instr := [.mov .esi (.mem (slot 48)), .alu .add .esi (.reg .esi)]

def seqs : List (Prog isa) → Prog isa
  | [] => .block []
  | [p] => p
  | p :: ps => .seq p (seqs ps)

end VG.Impl.MillerRabin.X86
