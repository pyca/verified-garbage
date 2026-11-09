module

public import VerifiedGarbage.Impl.ChaCha20.Arm

/-!
# ChaCha20 keystream XOR: 32-bit ARM implementation

`vg_chacha20_xor(state = r0, src = r1, len = r2, buf = r3, dst = r5)`
writes the `len` bytes at `src` XORed with the keystream to `dst`, which is
either `src` itself (in place) or a buffer apart from it (out of place).
This is an internal function, and AAPCS passes only four arguments in
registers, so `dst` comes in `r5`, a callee-saved register that our callers
can set: `vg_chacha20_apply` keeps the data there already, and
`vg_chacha20_poly1305_seal` and `_open` have it free.

For each 64 bytes of data (the last piece may be shorter),
`vg_chacha20_block(state, buf)` is called, the first `n = min(64, remaining)`
bytes of its output (the first 64 bytes of `buf`) are XORed with the next
bytes of `src` and written to `dst` a byte at a time, and the block counter
(word 12 of the state) is incremented modulo 2³².

The block function takes `state` in `r0` and `buf` in `r1`. It never writes
`r1`, so `buf` stays there throughout; it overwrites `r0`, so `state` is kept
in `r4` and copied to `r0` before each call. The source not yet processed,
its length and the destination are kept in `r5`, `r6` and `r7`. The block
function preserves `r4`–`r7` (and a call changes only `lr` and `r12` besides
what the callee writes). Our caller's `r4`–`r7`, and our return address
(`lr`, which each call replaces), are saved in `buf[256, 276)`, which is not
passed to the block function; so no stack is used. On return, `r0` is
`state`, `r1` is `buf` and `r5` is `dst` again.

The source is consumed through `r5` and the destination through `r7`, which
advance together, and the keystream through `r3 = buf + i`. Each byte of
the source is loaded before the destination's is stored, so in place the
source not yet consumed is intact. `remaining < 64` iff `remaining >> 6 = 0`,
and the loops count down to zero, tested with `cmp`/`subs` and `eq`/`ne`.
The branches are on the length only, and every address is a pointer plus a
constant or a count, so only the pointers and the length can affect timing.
-/

@[expose] public section

namespace VG.Impl.ChaCha20.Arm.Xor

open VG.Arm
open VG.Impl.ChaCha20.Arm (block)

/-- The registers saved in `buf`, and where. -/
def saved : List (Reg × Nat) := [(.r4, 256), (.r5, 260), (.r6, 264), (.lr, 268), (.r7, 272)]

/-- Save them, with `buf` in `r3`. -/
def save : List Instr := saved.map fun (r, d) => .str r .r3 d
/-- Restore them, with `buf` in `r1`. -/
def restore : List Instr := saved.map fun (r, d) => .ldr r .r1 d

/-- XORs the next `r2` bytes of the keystream (from `r3`) into the data (at
`r5`), advancing both: in place, for `vg_chacha20_apply`'s bytes of a
buffered block. -/
def xorLoop : Prog isa :=
  .loop (.block [.ldrb .r0 .r5 0, .ldrb .r12 .r3 0, .dp .eor .r0 .r0 (.reg .r12), .strb .r0 .r5 0,
    .dp .add .r5 .r5 (.imm 1), .dp .add .r3 .r3 (.imm 1), .subs .r2 .r2 (.imm 1)]) .ne

/-- XORs the next `r2` bytes of the source (at `r5`) with the keystream
(from `r3`) into the destination (at `r7`), advancing all three. -/
def xorTo : Prog isa :=
  .loop (.block [.ldrb .r0 .r5 0, .ldrb .r12 .r3 0, .dp .eor .r0 .r0 (.reg .r12), .strb .r0 .r7 0,
    .dp .add .r5 .r5 (.imm 1), .dp .add .r7 .r7 (.imm 1), .dp .add .r3 .r3 (.imm 1),
    .subs .r2 .r2 (.imm 1)]) .ne

/-- One block: the keystream into `buf`, `r2 = min(64, r6)` bytes of it
XORed with the source into the destination, and the counter incremented;
then whether data remains. -/
def body : Prog isa :=
  .seq (.block [.mov .r0 (.reg .r4)])
  (.seq (.call "vg_chacha20_block" block)
  (.seq (.block [.mov .r2 (.shifted .r6 .lsr 6), .cmp .r2 (.imm 0)])
  (.seq (.ite .eq (.block [.mov .r2 (.reg .r6)]) (.block [.mov .r2 (.imm 64)]))
  (.seq (.block [.dp .sub .r6 .r6 (.reg .r2), .mov .r3 (.reg .r1)])
  (.seq xorTo
    (.block [.ldr .r0 .r4 48, .dp .add .r0 .r0 (.imm 1), .str .r0 .r4 48, .cmp .r6 (.imm 0)]))))))

def xor : Prog isa :=
  .seq (.block (save ++ ([.mov .r7 (.reg .r5), .mov .r4 (.reg .r0), .mov .r5 (.reg .r1),
    .mov .r6 (.reg .r2), .mov .r1 (.reg .r3), .cmp .r6 (.imm 0)] : List Instr)))
  (.seq (.ite .eq (.block []) (.loop body .ne))
    (.block (.mov .r0 (.reg .r4) :: restore)))

end VG.Impl.ChaCha20.Arm.Xor
