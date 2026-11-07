module

public import VerifiedGarbage.Impl.AesGcm.RISCV64
public import VerifiedGarbage.Impl.Gather.RISCV64
public import VerifiedGarbage.Impl.StackScratch.RISCV64.Args

/-!
# AES-GCM decryption out of place, by a copy: RISC-V implementation

`vg_aes_gcm_open_to(ctx = a0, rounds = a1, nonce = a2, nonce_len = a3,
aad = a4, aad_len = a5, src = a6, len = a7, dst, dst_len, tag, tag_len)`,
its ninth to twelfth arguments in memory (RISC-V psABI, "Integer Calling
Convention": on the stack, from `sp` on entry): it copies the `len` bytes at
`src` to `dst` (`Impl/Gather/RISCV64.lean`'s `copySlice`, with `src`, `len`
and `dst` in `t0`, `t1` and `a6`), and decrypts them there in place with a
call of `vg_aes_gcm_open(ctx, rounds, nonce, nonce_len, aad, aad_len, dst,
len, tag, tag_len)`, whose `tag` and `tag_len` are its stack arguments. If it
returns 0 (the tag is wrong; `addiw` reads the low 32 bits of `a0`, the
result), `dst` holds the ciphertext again, and is zeroed a byte at a time
(`wipe`); `a0` is left as the call left it.

It allocates a frame of 32 bytes: the call's stack arguments `tag` and
`tag_len` at `sp` and `sp + 8`, and our return address, which the call
overwrites, at `sp + 16`. Our stack arguments `dst`, `dst_len`, `tag` and
`tag_len` are then at `sp + 32` … `sp + 56`. The copy writes only `t0`–`t2`
and `a6`: `ctx`, `rounds`, `nonce`, `nonce_len`, `aad`, `aad_len` and `len`
wait for the call where they are. Every register the function writes is
caller-saved, but `ra`, which it restores, and the branches are on `len`
alone, but the one after the call, on whether the tag is right.
-/

@[expose] public section

namespace VG.Impl.AesGcm.RISCV64.OpenTo

open VG.RISCV64
open VG.Impl.AesGcm.RISCV64 (mov)

/-- `vg_aes_gcm_open`, in its frame. -/
def openCode : Prog isa := Impl.StackScratch.RISCV64.withStackScratchArgs 2592 2 Impl.AesGcm.RISCV64.«open»

/-- Our return address into the frame (`t0` the stack pointer); `tag` and
`tag_len` into the call's stack arguments; `src`, `len` and `dst` into
`copySlice`'s registers. -/
def entry : List Instr :=
  [.addSp .t0 0, .store .d .ra .t0 16, .load .d .t1 .t0 48, .store .d .t1 .t0 0, .load .d .t1 .t0 56,
    .store .d .t1 .t0 8, .load .d .t1 .t0 32, mov .t0 .a6, mov .a6 .t1, mov .t1 .a7]

/-- The call's last register argument: `dst`, from our stack arguments; the
others are where they were on entry. -/
def callArgs : List Instr := [.addSp .t0 0, .load .d .a6 .t0 32]

/-- The low 32 bits of the result, sign-extended, into `t0`. -/
def test : List Instr := [.addiw .t0 .a0 0]

/-- `dst` in `t2`, `dst_len` (`len`) in `t3`, and zero in `t1`. -/
def wipeArgs : List Instr := [.addSp .t0 0, .load .d .t2 .t0 32, .load .d .t3 .t0 40, .li .t1 0]

/-- The `t3` bytes at `t2` zeroed, a byte at a time. -/
def wipeLoop : Prog isa :=
  .ite (.zero .t3) (.block [])
    (.loop (.block [.store .b .t1 .t2 0, .addi .t2 .t2 1, .addi .t3 .t3 (-1)]) (.nonzero .t3))

/-- The `len` bytes at `dst` zeroed. -/
def wipe : Prog isa := .seq (.block wipeArgs) wipeLoop

/-- After the call: `dst` wiped if it returned 0. -/
def after : Prog isa := .seq (.block test) (.ite (.zero .t0) wipe (.block []))

/-- Our return address back from the frame. -/
def ret : List Instr := [.addSp .t0 0, .load .d .ra .t0 16]

/-- `vg_aes_gcm_open_to`, calling `vg_aes_gcm_open`. -/
def openTo : Prog isa :=
  .frame (.alloc 32)
    (.seq (.block entry)
    (.seq Gather.RISCV64.copySlice
    (.seq (.block callArgs)
    (.seq (.call "vg_aes_gcm_open" openCode)
    (.seq after (.block ret))))))
    (.free 32)

end VG.Impl.AesGcm.RISCV64.OpenTo
