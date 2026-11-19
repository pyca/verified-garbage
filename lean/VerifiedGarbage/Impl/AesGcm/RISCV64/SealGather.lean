module

public import VerifiedGarbage.Impl.AesGcm.RISCV64
public import VerifiedGarbage.Impl.Gather.RISCV64
public import VerifiedGarbage.Impl.StackScratch.RISCV64.Args

/-!
# AES-GCM encryption out of place, from a list of slices: RISC-V implementation

`vg_aes_gcm_seal_gather(ctx = a0, rounds = a1, nonce = a2, nonce_len = a3,
aad = a4, aad_len = a5, src = a6, src_count = a7, dst, len, tag)`, its
ninth to eleventh arguments in memory (RISC-V psABI, "Integer Calling
Convention": on the stack, from `sp` on entry): it copies the slices `src`
lists, one after the other, to `dst` (`Impl/Gather/RISCV64.lean`, with
`src`, `src_count` and `dst` in `a4`, `a5` and `a6`), and encrypts them
there in place with a call of `vg_aes_gcm_seal(ctx, rounds, nonce,
nonce_len, aad, aad_len, dst, len, tag)`, whose `tag` is its stack argument.

It saves our return address, which the call overwrites, in a frame of 16
bytes (`push`, at `sp + 8`), whose first doubleword (at `sp`) is the call's
stack argument `tag`; our stack arguments `dst`, `len` and `tag` are then
at `sp + 16`, `sp + 24` and `sp + 32`. The gathering writes only `t0`–`t4`
and `a4`–`a6`: `ctx`, `rounds`, `nonce` and `nonce_len` wait for the call
where they are, `aad` in `t5`, `aad_len` in `t6` and `len` in `a7`.
-/

@[expose] public section

namespace VG.Impl.AesGcm.RISCV64.SealGather

open VG.RISCV64
open VG.Impl.AesGcm.RISCV64 (mov)

/-- `vg_aes_gcm_seal`, in its frame. -/
def sealCode : Prog isa := Impl.StackScratch.RISCV64.withStackScratchArgs 2576 1 Impl.AesGcm.RISCV64.«seal»

/-- `tag` into the call's stack argument (`t0` the stack pointer); `aad` and
`aad_len` into `t5` and `t6`; `src`, `src_count` and `dst` into `gather`'s
registers; and `len` into `a7`. -/
def entry : List Instr :=
  [.addSp .t0 0, .load .d .t1 .t0 32, .store .d .t1 .t0 0, mov .t5 .a4, mov .t6 .a5, mov .a4 .a6,
    mov .a5 .a7, .load .d .a6 .t0 16, .load .d .a7 .t0 24]

/-- The call's arguments: `aad` and `aad_len` back, and `dst` from our stack
arguments (`len` is in `a7`). -/
def callArgs : List Instr := [mov .a4 .t5, mov .a5 .t6, .addSp .t0 0, .load .d .a6 .t0 16]

/-- `vg_aes_gcm_seal_gather`. -/
def sealGather : Prog isa :=
  .frame (.push .ra)
    (.seq (.block entry)
    (.seq Gather.RISCV64.gather
    (.seq (.block callArgs)
      (.call "vg_aes_gcm_seal" sealCode))))
    (.pop .ra)

/-! ## Reading the key's bitsliced form

`vg_aes_gcm_seal_gather_bitsliced(ctx = a0, rounds = a1, nonce = a2,
nonce_len = a3, aad = a4, aad_len = a5, src = a6, src_count = a7, dst, len,
tag, bk)`: `sealGather`, with the buffer of the key context's bitsliced form
`bk` its twelfth argument, its fourth in memory, and a call of
`vg_aes_gcm_seal_bitsliced(ctx, rounds, nonce, nonce_len, aad, aad_len, dst,
len, tag, bk)`, whose `tag` and `bk` are its two stack arguments, as the
internal function `vg_aes_gcm_seal_bitsliced_core`: its code without the
clearing of the stack that the registered function ends with, which is ours
(as ChaCha20-Poly1305's `seal_gather` calls `vg_chacha20_poly1305_seal_core`).

Its frame is 32 bytes (`alloc`): the call's stack arguments `tag` and `bk`
at `sp` and `sp + 8`, and our return address, which the call overwrites, at
`sp + 16`, as in `Impl/CallWipe/RISCV64.lean`. Our stack arguments `dst`,
`len`, `tag` and `bk` are then at `sp + 32` to `sp + 56`.
-/

/-- `vg_aes_gcm_seal_bitsliced`, in its frame. -/
def sealBsCode : Prog isa := Impl.StackScratch.RISCV64.withStackScratchArgs 2592 2 Impl.AesGcm.RISCV64.sealBs

/-- The return address into the frame (`t0` the stack pointer); `tag` and
`bk` into the call's stack arguments; then as `entry`. -/
def entryBs : List Instr :=
  [.addSp .t0 0, .store .d .ra .t0 16, .load .d .t1 .t0 48, .store .d .t1 .t0 0, .load .d .t1 .t0 56,
    .store .d .t1 .t0 8, mov .t5 .a4, mov .t6 .a5, mov .a4 .a6, mov .a5 .a7, .load .d .a6 .t0 32,
    .load .d .a7 .t0 40]

/-- The call's arguments: `aad` and `aad_len` back, and `dst` from our stack
arguments (`len` is in `a7`). -/
def callArgsBs : List Instr := [mov .a4 .t5, mov .a5 .t6, .addSp .t0 0, .load .d .a6 .t0 32]

/-- The return address back from the frame. -/
def restoreBs : List Instr := [.addSp .t0 0, .load .d .ra .t0 16]

/-- `vg_aes_gcm_seal_gather_bitsliced`. -/
def sealGatherBs : Prog isa :=
  .frame (.alloc 32)
    (.seq (.block entryBs)
    (.seq Gather.RISCV64.gather
    (.seq (.block callArgsBs)
    (.seq (.call "vg_aes_gcm_seal_bitsliced_core" sealBsCode)
      (.block restoreBs)))))
    (.free 32)

end VG.Impl.AesGcm.RISCV64.SealGather
