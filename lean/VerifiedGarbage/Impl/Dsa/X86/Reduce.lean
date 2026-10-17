module

public import VerifiedGarbage.Impl.Mont.X86.Context

/-! # Streaming reduction of DSA's big-endian integers -/

@[expose] public section
namespace VG.Impl.Dsa.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic

/-- `k` modular doublings of slot six. -/
def doubles (n : Nat) : Nat → Prog isa
  | 0 => .block []
  | k + 1 => .seq (addW (contextMod n) (slot n 2) (slot n 6) (slot n 6) (slot n 6)) (doubles n k)

/-- Append a byte to the residue in slot six. Slot seven holds the byte
as an ordinary zero-padded integer. The modulus exceeds 255. -/
def reduceStep (n : Nat) : Prog isa :=
  .seq (doubles n 8) (addW (contextMod n) (slot n 2) (slot n 6) (slot n 6) (slot n 7))

end VG.Impl.Dsa.X86
