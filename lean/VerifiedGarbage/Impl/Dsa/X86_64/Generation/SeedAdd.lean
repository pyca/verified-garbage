module

public import VerifiedGarbage.TCB.X86_64.Isa

/-! # Wrap a DSA seed plus a public offset at its original byte width

`rsi` is the seed, `rdi` the destination, and `rax` the offset. Each byte
propagates carry toward the most significant end; overflow is discarded.
A public descending counter shares the byte step across the seed width.
The 20-byte SHA-1 path stays unrolled: a loop regressed the short
1024-bit parameter search. The 32-byte SHA-256 path uses the compact loop.
-/

@[expose] public section
namespace VG.Impl.Dsa.X86_64.Generation
open VG VG.X86_64

def seedAddByte (i : Nat) : List Instr :=
  [.movzx8 .rcx { base := .rsi, disp := i }, .alu .add .rax (.reg .rcx),
   .store8 { base := .rdi, disp := i } .rax, .shift .shr .rax 8]

def seedAddUnrolled : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (.block (seedAddByte n)) (seedAddUnrolled n)


/-- Process the last remaining byte, keeping the buffer bases fixed. -/
def seedAddStep : List Instr :=
  [.movzx8 .rcx { base := .rsi, index := some .rdx, disp := -1 },
   .alu .add .rax (.reg .rcx),
   .store8 { base := .rdi, index := some .rdx, disp := -1 } .rax,
   .shift .shr .rax 8, .alu .sub .rdx (.imm 1)]

/-- No byte is accessed for an empty seed. -/
def seedAddTail : Nat → Prog isa
  | 0 => .block []
  | _ + 1 => .loop (.block seedAddStep) .ne

def seedAdd (n : Nat) : Prog isa :=
  if n = 20 then seedAddUnrolled n
  else .seq (.block [.mov32 .rdx (.imm (BitVec.ofNat 32 n))]) (seedAddTail n)

end VG.Impl.Dsa.X86_64.Generation
