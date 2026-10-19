module

public import VerifiedGarbage.TCB.X86_64.Isa

/-! # Wrap a DSA seed plus a public offset at its original byte width

`rsi` is the seed, `rdi` the destination, and `rax` the offset. Each byte
propagates carry toward the most significant end; overflow is discarded.
The supported widths are emitted as fixed sequences of 20 or 32 bytes.
-/

@[expose] public section
namespace VG.Impl.Dsa.X86_64.Generation
open VG VG.X86_64

def seedAddByte (i : Nat) : List Instr :=
  [.movzx8 .rcx { base := .rsi, disp := i }, .alu .add .rax (.reg .rcx),
   .store8 { base := .rdi, disp := i } .rax, .shift .shr .rax 8]

def seedAdd : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (.block (seedAddByte n)) (seedAdd n)

end VG.Impl.Dsa.X86_64.Generation
