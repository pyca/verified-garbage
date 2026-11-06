module

public import VerifiedGarbage.Impl.Mont.X86.Context
public import VerifiedGarbage.Impl.Mont.X86.Words

/-! # Exponentiation by fixed 4-bit windows on 32-bit x86

The parts of a windowed exponentiation, which computes what `exponentiate` does, from the exponent's
top bits down: a table of the base's powers `0` to `15` in Montgomery form,
then for each four bits four squares and a multiplication by the table's
entry for them, read by a masked scan of the whole table. The exponent's
words are shifted up by four bits per window; every count and address is
public.
-/

@[expose] public section
namespace VG.Impl.Mont.X86.Dynamic
open VG VG.X86 VG.Impl.Mont VG.Impl.Mont.X86

/-- The workspace word holding the current window. -/
def windowOffset : Nat := 4

/-- The table's entry `j`, of `n` 64-bit words, at `tab`. -/
def entry (n tab j : Nat) : Nat := tab + 8 * n * j

/-- Copy `n` 64-bit words. -/
def copyWords (n src dst : Nat) : Prog isa :=
  .seq (.block [.mov .ecx (.imm 0)]) (selectsW (2 * n) src src dst)

/-- ECX all ones exactly when the window is `j` (below 16). -/
def windowMask (j : Nat) : List Instr :=
  [.mov .eax (.mem (sc windowOffset)), .alu .xor .eax (.imm (BitVec.ofNat 32 j)),
   .alu .sub .eax (.imm 1), .shift .shr .eax 31, .mov .ecx (.imm 0), .alu .sub .ecx (.reg .eax)]

def square (n : Nat) : Prog isa := mul (contextMod n) 0 (slot n 2) (slot n 6) (slot n 6) (slot n 6)

end VG.Impl.Mont.X86.Dynamic
