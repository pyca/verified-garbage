module

public import VerifiedGarbage.Impl.AesGcm.AArch64.SealGather

/-!
# AES-GCM decryption out of place, by a copy: AArch64 implementation

`vg_aes_gcm_open_to(ctx = x0, rounds = x1, nonce = x2, nonce_len = x3,
aad = x4, aad_len = x5, src = x6, len = x7, dst = [sp], dst_len = [sp + 8],
tag = [sp + 16], tag_len = [sp + 24])`, generic over the implementation of
`vg_aes_gcm_open` it calls (`f`): it copies the `len` bytes at `src` to
`dst` (`SealGather.copySlice`, 16 bytes at a time through `v0`, then the
last `len mod 16` eight, four and one at a time), and decrypts them there in
place with a call of
`vg_aes_gcm_open(ctx, rounds, nonce, nonce_len, aad, aad_len, dst, len, tag, tag_len)`.
If it returns 0 (the tag is wrong), `dst` holds the ciphertext again, and is
zeroed a byte at a time (`wipe`); `x0` is left as the call left it, 0.

It allocates a frame of 32 bytes: `tag` and `tag_len`, the call's stack
arguments, at `sp` and `sp + 8`, and our return address, which the call
(`bl`) overwrites in `x30`, at `sp + 16`; our stack arguments are then at
`sp + 32` … `sp + 56`. Every register the copy and the wipe write is
caller-saved, and their branches are on `len` alone; the branch after the
call is on whether the tag is right.
-/

@[expose] public section

namespace VG.Impl.AesGcm.AArch64.OpenTo

open VG.AArch64
open VG.Impl.AesGcm.AArch64.SealGather (copySlice)

/-- Our return address at `sp + 16`, `tag` and `tag_len` (our stack
arguments at `sp + 48` and `sp + 56`) at `sp` and `sp + 8`, and the copy's
arguments: `dst` in `x11`, `src` in `x12` and `len` in `x13`. -/
def entry : List Instr :=
  [.addSp .x16 0, .str .x .x30 .x16 16, .ldrSp .x17 48, .str .x .x17 .x16 0, .ldrSp .x17 56,
   .str .x .x17 .x16 8, .ldrSp .x11 32, .addImm .x .x12 .x6 0, .addImm .x .x13 .x7 0]

/-- `dst` as the call's `data`; `len` is still in `x7`. -/
def callArgs : List Instr := [.ldrSp .x6 32]

/-- `dst` in `x9`, `dst_len` (`len`) in `x10`, and zero in `x11`. -/
def wipeArgs : List Instr := [.ldrSp .x9 32, .ldrSp .x10 40, .movz .x .x11 0 0]

/-- The `x10` bytes at `x9` zeroed, a byte at a time. -/
def wipeLoop : Prog isa :=
  .ite (.zero .x .x10) (.block [])
    (.loop (.block [.strb .x11 .x9 0, .addImm .x .x9 .x9 1, .subImm .x .x10 .x10 1])
      (.nonzero .x .x10))

/-- The `len` bytes at `dst` zeroed. -/
def wipe : Prog isa := .seq (.block wipeArgs) wipeLoop

/-- After the call: `dst` wiped if it returned 0. -/
def after : Prog isa := .ite (.zero .w .x0) wipe (.block [])

/-- `vg_aes_gcm_open_to`, calling `f`, an implementation of `vg_aes_gcm_open`. -/
def openTo (f : Fn) : Prog isa :=
  .frame (.alloc 32)
    (.seq (.block entry)
    (.seq copySlice
    (.seq (.block callArgs)
    (.seq (.call f.name f.code)
    (.seq after
      (.block [.ldrSp .x30 16]))))))
    (.free 32)

end VG.Impl.AesGcm.AArch64.OpenTo
