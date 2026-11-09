module

public import VerifiedGarbage.Impl.ChaCha20.RISCV64

/-!
# ChaCha20 keystream XOR: RISC-V implementation

`vg_chacha20_xor(state = a0, src = a1, len = a2, buf = a3, dst = a4)`
writes the `len` bytes at `src` XORed with the keystream to `dst`, which is
either `src` itself (in place) or a buffer apart from it (out of place).

The structure of the PPC64LE implementation: for each 64 bytes of data (the
last piece may be shorter), `vg_chacha20_block(state, buf)` is called, the
first `n = min(64, remaining)` bytes of its output (the first 64 bytes of
`buf`) are XORed with the next bytes of `src` and written to `dst`, a byte
at a time (or a doubleword at a time, `xorAny`), and the block counter (word
12 of the state, read and written a byte at a time, since the contract
states no alignment for `state`) is incremented modulo 2³².

The block function takes `state` in `a0` and `buf` in `a1`, and writes
neither (it writes `t0`–`t6`, `a2`–`a7` and `s0`–`s4`, which it restores,
and a call changes `ra` and `t0`–`t6`), so they stay there throughout. The
source not yet processed, its length and the destination are kept across
the calls in `s5`, `s6` and `s7`, which the block function preserves. Our
caller's values of those, and our return address (`ra`, which each call
replaces), are saved as doublewords at `buf + 256` rounded up to a multiple
of 8, within `buf[256, 320)`, which is not passed to the block function; so
no stack is used.

The source is consumed through `s5` and the destination through `s7`, which
advance together, and the keystream through `t2 = buf + i`. Each byte (or
doubleword) of the source is loaded before the destination's is stored, so
in place the source not yet consumed is intact. `remaining < 64` iff
`remaining >> 6 = 0`, and the loops
count down to zero. The branches are on the length only, and every address
is a pointer plus a constant or a count, so only the pointers and the
length can affect timing.
-/

@[expose] public section

namespace VG.Impl.ChaCha20.RISCV64.Xor

open VG.RISCV64
open VG.Impl.Words.RISCV64
open VG.Impl.ChaCha20.RISCV64 (block)

/-- `mv d, n` (`addi d, n, 0`). -/
def mov (d n : Reg) : Instr := .addi d n 0

/-- `t0 :=` `n + 256` rounded up to a multiple of 8 (`(n + 263) & -8`). -/
def savePtr (n : Reg) : List Instr := [.addi .t0 n 263, .logicImm .and .t0 .t0 (-8)]

/-- Save our caller's `s5`, `s6` and `s7` and our return address, with `buf`
in `a3`. -/
def save : List Instr :=
  savePtr .a3 ++ [.store .d .s5 .t0 0, .store .d .s6 .t0 8, .store .d .ra .t0 16, .store .d .s7 .t0 24]

/-- Restore them, with `buf` in `a1`. -/
def restore : List Instr :=
  savePtr .a1 ++ [.load .d .ra .t0 16, .load .d .s5 .t0 0, .load .d .s6 .t0 8, .load .d .s7 .t0 24]

/-- XORs the next `a2` bytes of the source (at `s5`) with the keystream
(from `t2`) into the destination (at `s7`), advancing all three. -/
def xorLoop : Prog isa :=
  .loop (.block [.load .b .t3 .s5 0, .load .b .t4 .t2 0, .logic .xor .t3 .t3 .t4, .store .b .t3 .s7 0,
    .addi .s5 .s5 1, .addi .s7 .s7 1, .addi .t2 .t2 1, .addi .a2 .a2 (-1)]) (.nonzero .a2)

/-- `xorLoop` for `a2` a multiple of 8 and the source, the keystream and the
destination 8-byte aligned, a doubleword at a time. -/
def xorWide : Prog isa :=
  .loop (.block [.load .d .t3 .s5 0, .load .d .t4 .t2 0, .logic .xor .t3 .t3 .t4, .store .d .t3 .s7 0,
    .addi .s5 .s5 8, .addi .s7 .s7 8, .addi .t2 .t2 8, .addi .a2 .a2 (-8)]) (.nonzero .a2)

/-- `xorWide` if the source, the keystream, the length and the destination
are multiples of 8 (`t3 = (((s5 | t2) | a2) | s7) & 7` is zero), else
`xorLoop`. -/
def xorAny : Prog isa :=
  .seq (.block [.logic .or .t3 .s5 .t2, .logic .or .t3 .t3 .a2, .logic .or .t3 .t3 .s7,
    .logicImm .and .t3 .t3 7])
    (.ite (.zero .t3) xorWide xorLoop)

/-- The block counter (word 12 of the state, 4-byte aligned) incremented. -/
def next : List Instr := [.load .w .t1 .a0 48, .addi .t1 .t1 1, .store .w .t1 .a0 48]

/-- One block: the keystream into `buf`, `a2 = min(64, s6)` bytes of it
XORed with the source into the destination, and the counter incremented. -/
def body : Prog isa :=
  .seq (.call "vg_chacha20_block" block)
  (.seq (.block [.shift .srl .d .t1 .s6 6, mov .a2 .s6])
  (.seq (.ite (.zero .t1) (.block []) (.block [.li .a2 64]))
  (.seq (.block [.sub .s6 .s6 .a2, mov .t2 .a1])
  (.seq xorAny (.block next)))))

def xor : Prog isa :=
  .seq (.block (save ++ [mov .s5 .a1, mov .s6 .a2, mov .s7 .a4, mov .a1 .a3]))
  (.seq (.ite (.zero .s6) (.block []) (.loop body (.nonzero .s6)))
    (.block restore))

end VG.Impl.ChaCha20.RISCV64.Xor
