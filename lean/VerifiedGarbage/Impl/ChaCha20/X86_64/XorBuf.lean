module
public import VerifiedGarbage.TCB.X86_64.Isa
import VerifiedGarbage.Impl.ChaCha20.X86_64


/-!
# XORing keystream from a buffer into the data, eight bytes at a time

`xorBufTo d s b` writes the `rdx` bytes at `s` (the source) XORed with the
`rdx` bytes at `b` (keystream, in a buffer) to the `rdx` bytes at `d` (the
destination: `s` itself, or apart from it): eight bytes at a time while at
least eight remain, then a byte at a time, each loaded from the source before
it is stored to the destination; `xorBuf d b` does it in place. `rcx` counts
the bytes done; `rax` counts down the whole quadwords left (from `rdx / 8`)
and then serves, with `r8`, as scratch.

The branches are on `rcx`, `rax` and `rdx` only, which depend on the length
alone, and every address is `d` or `b` plus `rcx`, so only the pointers and
the length can affect timing.
-/

@[expose] public section

namespace VG.Impl.ChaCha20.X86_64.XorBuf

open VG.X86_64

/-- `[base + rcx]`. -/
def idx (base : Reg) : MemOp := { base := base, index := some .rcx }

/-- The quadword at `s + rcx` XORed with that at `b + rcx`, to `d + rcx`. -/
def qBody (d s b : Reg) : List Instr :=
  [.mov .r8 (.mem (idx s)), .alu .xor .r8 (.mem (idx b)), .store (idx d) .r8,
   .alu .add .rcx (.imm 8), .alu .sub .rax (.imm 1)]

/-- The byte at `s + rcx` XORed with that at `b + rcx`, to `d + rcx`. -/
def bBody (d s b : Reg) : List Instr :=
  [.movzx8 .rax (idx s), .movzx8 .r8 (idx b), .alu .xor .rax (.reg .r8), .store8 (idx d) .rax,
   .alu .add .rcx (.imm 1), .alu .cmp .rcx (.reg .rdx)]

def xorBufTo (d s b : Reg) : Prog isa :=
  .seq (.block [.mov32 .rcx (.imm 0), .mov .rax (.reg .rdx), .shift .shr .rax 3])
  (.seq (.ite .e (.block []) (.loop (.block (qBody d s b)) .ne))
  (.seq (.block [.alu .cmp .rcx (.reg .rdx)])
    (.ite .e (.block []) (.loop (.block (bBody d s b)) .ne))))

/-- `[rsi + ix + d]`: where the vector implementations store the
destination's byte `d` past the source's in `rsi`, `ix` (`r11`) holding the
destination's distance from the source; `[rsi + d]` in place (`none`). -/
def atDst (ix : Option Reg) (d : Nat) : MemOp := { base := .rsi, index := ix, disp := d }

/-- `r11 = r8 - rsi`: the destination's distance from the source, which the
vector implementations compute on entry and never write again (`atDst`). -/
def delta : List Instr := [.mov .r11 (.reg .r8), .alu .sub .r11 (.reg .rsi)]

/-- `xorBufTo` in place. -/
def xorBuf (d b : Reg) : Prog isa := xorBufTo d d b

/-- The `2 ^ w` bytes at `s + rcx` XORed with those at `rsi + rcx`, to
`d + rcx`, through `xmm0` and `xmm1` (or `ymm`, `zmm`), for `w` = 4, 5 or
6. -/
def xDataTo : Nat → Reg → Reg → List Instr
  | 4, d, s => [.movdquLoad .xmm0 (idx s), .movdquLoad .xmm1 (idx .rsi),
      .xop (.bin .pxor .xmm0 .xmm1), .movdquStore (idx d) .xmm0]
  | 5, d, s => [.vmovdquLoad .l256 .xmm0 (idx s),
      .vmovdquLoad .l256 .xmm1 (idx .rsi), .vop (.vbin .vpxor .l256 .xmm0 .xmm0 .xmm1),
      .vmovdquStore .l256 (idx d) .xmm0]
  | _, d, s => [.vmovdqu32Load .xmm0 (idx s), .vmovdqu32Load .xmm1 (idx .rsi),
      .zop (.zbin .vpxord .xmm0 .xmm0 .xmm1), .vmovdqu32Store (idx d) .xmm0]

/-- `xDataTo` in place. -/
def xData (w : Nat) (d : Reg) : List Instr := xDataTo w d d

/-- `xDataTo`, with `rcx` advanced past the bytes and `rax` counting down. -/
def xBodyTo (w : Nat) (d s : Reg) : List Instr :=
  xDataTo w d s ++ [.alu .add .rcx (.imm (BitVec.ofNat 32 (2 ^ w))), .alu .sub .rax (.imm 1)]

/-- `xBodyTo` in place. -/
def xBody (w : Nat) (d : Reg) : List Instr := xBodyTo w d d

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

/-- Writes the `rdx` bytes at `s` XORed with the `rdx` bytes at `rsi` to
the `rdx` bytes at `d` (`s` itself, or apart from it), as `xorBufX` does in
place, the rest by `XorBuf.xorBufTo` from `rdi = d + rcx`, `s + rcx` (so `s`
is advanced) and `rsi + rcx`. -/
def xorBufXTo (w : Nat) (d s : Reg) : Prog isa :=
  .seq (.block [.mov32 .rcx (.imm 0), .mov .rax (.reg .rdx), .shift .shr .rax w])
  (.seq (.ite .e (.block []) (.loop (.block (xBodyTo w d s)) .ne))
  (.seq (.block [.mov .rdi (.reg d), .alu .add .rdi (.reg .rcx), .alu .add s (.reg .rcx),
    .alu .add .rsi (.reg .rcx), .alu .sub .rdx (.reg .rcx)])
    (xorBufTo .rdi s .rsi)))

end VG.Impl.ChaCha20.X86_64.XorBuf
