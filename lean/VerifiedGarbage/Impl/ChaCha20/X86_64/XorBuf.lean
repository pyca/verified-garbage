module
public import VerifiedGarbage.TCB.X86_64.Isa
import VerifiedGarbage.Impl.ChaCha20.X86_64


/-!
# XORing keystream from a buffer into the data, eight bytes at a time

`xorBuf d b` XORs the `rdx` bytes at `b` (keystream, in a buffer) into the
`rdx` bytes at `d` (the data): eight bytes at a time while at least eight
remain, then a byte at a time. `rcx` counts the bytes done; `rax` counts
down the whole quadwords left (from `rdx / 8`) and then serves, with `r8`,
as scratch.

The branches are on `rcx`, `rax` and `rdx` only, which depend on the length
alone, and every address is `d` or `b` plus `rcx`, so only the pointers and
the length can affect timing.
-/

@[expose] public section

namespace VG.Impl.ChaCha20.X86_64.XorBuf

open VG.X86_64

/-- `[base + rcx]`. -/
def idx (base : Reg) : MemOp := { base := base, index := some .rcx }

/-- XOR the quadword at `b + rcx` into that at `d + rcx`. -/
def qBody (d b : Reg) : List Instr :=
  [.mov .r8 (.mem (idx d)), .alu .xor .r8 (.mem (idx b)), .store (idx d) .r8,
   .alu .add .rcx (.imm 8), .alu .sub .rax (.imm 1)]

/-- XOR the byte at `b + rcx` into that at `d + rcx`. -/
def bBody (d b : Reg) : List Instr :=
  [.movzx8 .rax (idx d), .movzx8 .r8 (idx b), .alu .xor .rax (.reg .r8), .store8 (idx d) .rax,
   .alu .add .rcx (.imm 1), .alu .cmp .rcx (.reg .rdx)]

def xorBuf (d b : Reg) : Prog isa :=
  .seq (.block [.mov32 .rcx (.imm 0), .mov .rax (.reg .rdx), .shift .shr .rax 3])
  (.seq (.ite .e (.block []) (.loop (.block (qBody d b)) .ne))
  (.seq (.block [.alu .cmp .rcx (.reg .rdx)])
    (.ite .e (.block []) (.loop (.block (bBody d b)) .ne))))

/-- The bytes `xorBuf` leaves after its quadwords: from `rcx` to `rdx`, one at a time. -/
def bytes (d b : Reg) : Prog isa :=
  .seq (.block [.alu .cmp .rcx (.reg .rdx)]) (.ite .e (.block []) (.loop (.block (bBody d b)) .ne))

/-- `xorBuf`, with `big` from 64 bytes on: its prologue, then fewer than 8
bytes one at a time, fewer than 64 by its quadwords and bytes, otherwise
`big` (with `rcx`, `rax` and the flags written). Below 8 bytes it runs
`xorBuf`'s instructions, and from 8 to 63 two more (`cmp rax, 8`, `jb`). -/
def xorBufS (big : Prog isa) (d b : Reg) : Prog isa :=
  .seq (.block [.mov32 .rcx (.imm 0), .mov .rax (.reg .rdx), .shift .shr .rax 3])
  (.ite .e (bytes d b)
    (.seq (.block [.alu .cmp .rax (.imm 8)])
      (.ite .b (.seq (.loop (.block (qBody d b)) .ne) (bytes d b)) big)))

/-- XOR the `2 ^ w` bytes at `rsi + rcx` into those at `d + rcx`, through
`xmm0` and `xmm1` (or `ymm`, `zmm`), for `w` = 4, 5 or 6. -/
def xData : Nat → Reg → List Instr
  | 4, d => [.movdquLoad .xmm0 (idx d), .movdquLoad .xmm1 (idx .rsi),
      .xop (.bin .pxor .xmm0 .xmm1), .movdquStore (idx d) .xmm0]
  | 5, d => [.vmovdquLoad .l256 .xmm0 (idx d),
      .vmovdquLoad .l256 .xmm1 (idx .rsi), .vop (.vbin .vpxor .l256 .xmm0 .xmm0 .xmm1),
      .vmovdquStore .l256 (idx d) .xmm0]
  | _, d => [.vmovdqu32Load .xmm0 (idx d), .vmovdqu32Load .xmm1 (idx .rsi),
      .zop (.zbin .vpxord .xmm0 .xmm0 .xmm1), .vmovdqu32Store (idx d) .xmm0]

/-- `xData`, with `rcx` advanced past the bytes and `rax` counting down. -/
def xBody (w : Nat) (d : Reg) : List Instr :=
  xData w d ++ [.alu .add .rcx (.imm (BitVec.ofNat 32 (2 ^ w))), .alu .sub .rax (.imm 1)]

/-- XORs the `rdx` bytes at `rsi` into the `rdx` bytes at `d`: `2 ^ w` at a
time while at least that many remain (`rcx` counting the bytes done, `rax`
the words left), then the rest by `XorBuf.xorBuf` from `rdi = d + rcx` and
`rsi + rcx`. -/
def xorBufX (w : Nat) (d : Reg) : Prog isa :=
  .seq (.block [.mov32 .rcx (.imm 0), .mov .rax (.reg .rdx), .shift .shr .rax w])
  (.seq (.ite .e (.block []) (.loop (.block (xBody w d)) .ne))
  (.seq (.block [.mov .rdi (.reg d), .alu .add .rdi (.reg .rcx), .alu .add .rsi (.reg .rcx),
    .alu .sub .rdx (.reg .rcx)])
    (xorBuf .rdi .rsi)))

/-- The `rdx` bytes of keystream in a buffer at `r9` XORed into the data at
`rsi`, by `xorBufX w` with the data's address in `r10`: `2 ^ w` bytes at a
time while at least that many remain, then eight and one at a time. -/
def fromBufX (w : Nat) : Prog isa :=
  .seq (.block [.mov .r10 (.reg .rsi), .mov .rsi (.reg .r9)]) (xorBufX w .r10)

end VG.Impl.ChaCha20.X86_64.XorBuf
