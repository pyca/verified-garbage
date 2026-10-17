module

public import VerifiedGarbage.Impl.Dsa.X86.Reduce

/-! # Bounded streaming reduction from an external byte string -/

@[expose] public section
namespace VG.Impl.Dsa.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic

/-- Fetch the byte at `esi` into the low word of slot seven. Its higher
words have been cleared by the streaming initializer. -/
def fetchByte (n : Nat) : List Instr :=
  [.movzx8 .eax (at_ .esi 0), .store (sc (slot n 7)) .eax]

/-- One byte: `esi` moves up to the end, in `ebx`. -/
def streamStep (n : Nat) : Prog isa :=
  .seq (.block (fetchByte n)) (.seq (reduceStep n)
    (.block [.alu .add .esi (.imm 1), .alu .cmp .esi (.reg .ebx)]))

/-- Reduce the public byte count `len` (an immediate, or a saved length),
including zero, at `esi`, modulo the initialized runtime modulus. Result:
slot six. The source and its end stay in registers, so no public value is
read back from memory in the loop. -/
def reduceStream (n : Nat) (len : Src) : Prog isa :=
  .seq (zerosW (slot n 6) (2 * n)) <|
  .seq (zerosW (slot n 7) (2 * n)) <|
  .seq (.block [.mov .ebx len]) <|
  .seq (.block [.alu .add .ebx (.reg .esi), .alu .cmp .esi (.reg .ebx)])
    (.ite .e (.block []) (.loop (streamStep n) .ne))

end VG.Impl.Dsa.X86
