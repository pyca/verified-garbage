module

public import VerifiedGarbage.Impl.Mont.X86.Context

/-! # Streaming reduction of DSA's big-endian integers -/

@[expose] public section
namespace VG.Impl.Dsa.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic

/-- A fixed public number of modular doublings, preserving the byte pointer. -/
def doubles (n out : Nat) : Nat → List Instr
  | 0 => []
  | k + 1 => doubles n out k ++ add (contextMod n) (slot n 2) out out out

/-- Append a byte to the residue in slot six. Slot seven holds the byte
as an ordinary zero-padded integer. The modulus exceeds 255. -/
def reduceStep (n : Nat) : List Instr :=
  doubles n (slot n 6) 8 ++ add (contextMod n) (slot n 2) (slot n 6) (slot n 6) (slot n 7)

end VG.Impl.Dsa.X86
