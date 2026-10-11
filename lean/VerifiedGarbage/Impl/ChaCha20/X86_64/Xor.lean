module

public import VerifiedGarbage.Impl.ChaCha20.X86_64.XorBuf

/-!
# ChaCha20 keystream XOR: x86-64 implementation

`vg_chacha20_xor(state = rdi, data = rsi, len = rdx, buf = rcx)`.

For each 64 bytes of data (the last piece may be shorter),
`vg_chacha20_block(state, buf)` is called, the first `n = min(64, remaining)`
bytes of its output (the first 64 bytes of `buf`) are XORed into the data,
eight bytes at a time and then a byte at a time (`XorBuf.xorBuf`), and the
block counter (word 12 of the state) is incremented modulo 2³².

`buf` is in `rsi` throughout: the block function takes it there and never
writes `rsi`. The other pointers and the remaining length are kept across the
calls in `rbx` (`state`), `rbp` (the data not yet processed) and `r12` (its
length), which the block function preserves; our caller's values of those are
saved in `buf[256, 280)`, which is not passed to the block function.

The branches are on the length only, and every address is a pointer plus a
constant or a count, so only the pointers and the length can affect timing.
-/

@[expose] public section

namespace VG.Impl.ChaCha20.X86_64.Xor

open VG.X86_64
open VG.Impl.ChaCha20.X86_64 (at_ block)

def saved : List (Reg × Nat) := [(.rbx, 256), (.rbp, 264), (.r12, 272)]

def save : List Instr := saved.map fun (r, d) => .store (at_ .rcx d) r
def restore : List Instr := saved.map fun (r, d) => .mov r (.mem (at_ .rsi d))

/-- One block: the keystream into `buf`, `rdx = min(64, r12)` bytes of it
XORed into the data, and the counter incremented. -/
def body : Prog isa :=
  .seq (.block [.mov .rdi (.reg .rbx)])
  (.seq (.call "vg_chacha20_block" block)
  (.seq (.block [.mov .rdx (.reg .r12), .alu .cmp .r12 (.imm 64)])
  (.seq (.ite .b (.block []) (.block [.mov32 .rdx (.imm 64)]))
  (.seq (XorBuf.xorBuf .rbp .rsi)
    (.block [.mov32 .rax (.mem (at_ .rbx 48)), .alu32 .add .rax (.imm 1),
      .store32 (at_ .rbx 48) .rax, .alu .add .rbp (.reg .rdx), .alu .sub .r12 (.reg .rdx)])))))

def xor : Prog isa :=
  .seq (.block (save ++ ([.mov .rbx (.reg .rdi), .mov .rbp (.reg .rsi), .mov .r12 (.reg .rdx),
    .mov .rsi (.reg .rcx), .alu .test .r12 (.reg .r12)] : List Instr)))
  (.seq (.ite .e (.block []) (.loop body .ne))
    (.block restore))

end VG.Impl.ChaCha20.X86_64.Xor
