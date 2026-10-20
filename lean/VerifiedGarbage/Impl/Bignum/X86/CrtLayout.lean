module

public import VerifiedGarbage.Impl.Mont.X86.Context

/-! # A single arithmetic context and preserved CRT components

The first nine slots are the Montgomery context. Slots nine through nineteen
preserve the imported components, factor residues, full product and result.
Each slot has enough room for a double-width integer and a guard word.
-/

@[expose] public section
namespace VG.Impl.Bignum.X86.Crt
open VG.Impl.Mont.X86.Dynamic

def modulusSlot : Nat := 9
def pSlot : Nat := 10
def qSlot : Nat := 11
def dpSlot : Nat := 12
def dqSlot : Nat := 13
def inverseSlot : Nat := 14
def inputSlot : Nat := 15
def mpSlot : Nat := 16
def mqSlot : Nat := 17
def productSlot : Nat := 18
def resultSlot : Nat := 19

/-- The slots, and the narrow exponentiation's table of 16 entries of
`half n` words after them. -/
def size (n : Nat) : Nat := slot n 28
def acceptanceOffset : Nat := 8
def multiplierOffset : Nat := 48

end VG.Impl.Bignum.X86.Crt
