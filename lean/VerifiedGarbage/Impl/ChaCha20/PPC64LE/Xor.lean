module

public import VerifiedGarbage.Impl.ChaCha20.PPC64LE

/-!
# ChaCha20 keystream XOR, a block at a time: PPC64LE implementation

`vg_chacha20_xor(state = r3, src = r4, len = r5, buf = r6, dst = r7)`'s
contract, a block at a time: it writes the `len` bytes at `src` XORed with
the keystream to `dst`, which is either `src` itself (in place) or a buffer
apart from it (out of place). `vg_chacha20_xor` is `Vmx4.xor`, which runs
this on what its four-block chunks leave.

For each 64 bytes of data (the last piece may be shorter),
`vg_chacha20_block(state, buf)` is called, the first `n = min(64, remaining)`
bytes of its output (the first 64 bytes of `buf`) are XORed with the next
bytes of `src` and written to `dst`, eight bytes at a time for complete
blocks, or bytewise for a partial block,
and the block counter (word 12 of the state) is incremented
modulo 2³².

The block function takes `state` in `r3` and `buf` in `r4`, and writes
neither (it writes only `r0`, `r5`–`r12` and `r14`–`r21`, and a call changes
`r0`, `r11`, `r12` and the link register), so they stay there throughout.
The source not yet processed, its length and the destination are kept
across the calls in `r22`, `r23` and `r30`, which the block function
preserves. Our caller's values of those, and our return address (the link
register, which each call replaces, moved to `r0`), are saved in
`buf[256, 288)`, which is not passed to the block function; so no stack is
used.

Only register-plus-displacement addressing is used: the source is consumed
through `r22` and the destination through `r30`, which advance together, and
the keystream through `r7 = buf + i`. Each byte (or doubleword) of the
source is loaded before the destination's is stored, so in place the source
not yet consumed is intact.
`remaining < 64` iff `remaining >> 6 = 0`, and the loops count down to
zero. The branches are on the length only, and every address is a pointer
plus a constant or a count, so only the pointers and the length can affect
timing.
-/

@[expose] public section

namespace VG.Impl.ChaCha20.PPC64LE.Xor

open VG.PPC64LE
open VG.Impl.ChaCha20.PPC64LE (block)

/-- `mr d, n` (as `addi d, n, 0`; `n` is not `r0`). -/
def mov (d n : Reg) : Instr := .addi d n 0

/-- Save our caller's `r22`, `r23` and `r30` and our return address, with
`buf` in `r6`. -/
def save : List Instr :=
  [.store .d .r22 .r6 256, .store .d .r23 .r6 264, .mflr .r0, .store .d .r0 .r6 272,
    .store .d .r30 .r6 280]

/-- Restore them, with `buf` in `r4`. -/
def restore : List Instr :=
  [.load .d .r0 .r4 272, .mtlr .r0, .load .d .r22 .r4 256, .load .d .r23 .r4 264,
    .load .d .r30 .r4 280]

/-- XORs the next `r5` bytes of the source (at `r22`) with the keystream
(from `r7`) into the destination (at `r30`), advancing all three. -/
def xorBytes : Prog isa :=
  .loop (.block [.lbz .r6 .r22 0, .lbz .r8 .r7 0, .logic .xor .r6 .r6 .r8, .stb .r6 .r30 0,
    .addi .r22 .r22 1, .addi .r30 .r30 1, .addi .r7 .r7 1, .subi .r5 .r5 1]) (.nonzero .d .r5)

/-- XOR a complete block with eight doubleword operations. The load/store
addresses need not be aligned; only the public length selects this path. -/
def xorWords : Prog isa :=
  .loop (.block [.load .d .r6 .r22 0, .load .d .r8 .r7 0, .logic .xor .r6 .r6 .r8,
    .store .d .r6 .r30 0, .addi .r22 .r22 8, .addi .r30 .r30 8, .addi .r7 .r7 8, .subi .r5 .r5 8])
    (.nonzero .d .r5)

/-- Complete blocks use doublewords; the final partial block uses bytes. -/
def xorLoop : Prog isa :=
  .seq (.block [.lsr .d .r9 .r5 6])
    (.ite (.zero .d .r9) xorBytes xorWords)

/-- One block: the keystream into `buf`, `r5 = min(64, r23)` bytes of it
XORed with the source into the destination, and the counter incremented. -/
def body : Prog isa :=
  .seq (.call "vg_chacha20_block" block)
  (.seq (.block [.lsr .d .r9 .r23 6, mov .r5 .r23])
  (.seq (.ite (.zero .d .r9) (.block []) (.block [.li .r5 64]))
  (.seq (.block [.sub .r23 .r23 .r5, mov .r7 .r4])
  (.seq xorLoop
    (.block [.load .w .r8 .r3 48, .addi .r8 .r8 1, .store .w .r8 .r3 48])))))

def xor : Prog isa :=
  .seq (.block (save ++ [mov .r22 .r4, mov .r23 .r5, mov .r30 .r7, mov .r4 .r6]))
  (.seq (.ite (.zero .d .r23) (.block []) (.loop body (.nonzero .d .r23)))
    (.block restore))

end VG.Impl.ChaCha20.PPC64LE.Xor
