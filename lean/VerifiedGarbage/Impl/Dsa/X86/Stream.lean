module

public import VerifiedGarbage.Impl.Dsa.X86.Reduce

/-! # Bounded streaming reduction from an external byte string -/

@[expose] public section
namespace VG.Impl.Dsa.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic

/-- The public source pointer occupies a reserved header word. -/
def sourcePointer : Nat := 20

/-- Fetch byte `esi` of the source into the low word of slot seven. Its
higher words have been cleared by the streaming initializer. -/
def fetchByte (n : Nat) : List Instr :=
  [.mov .ebp (.mem (sc sourcePointer)), .alu .add .ebp (.reg .esi),
    .movzx8 .eax (at_ .ebp 0), .store (sc (slot n 7)) .eax]

def streamStep (n len : Nat) : List Instr :=
  fetchByte n ++ reduceStep n ++
    [.alu .add .esi (.imm 1), .alu .cmp .esi (.imm (BitVec.ofNat 32 len))]

/-- Reduce any public byte count, including zero, modulo the initialized
runtime modulus. Result: slot six. Input address: header word twenty. -/
def reduceStream (n len : Nat) : Prog isa :=
  .seq (.block (zeros (slot n 6) (2 * n) ++ zeros (slot n 7) (2 * n) ++ [.mov .esi (.imm 0)]))
    (if len = 0 then .block [] else .loop (.block (streamStep n len)) .ne)

end VG.Impl.Dsa.X86
