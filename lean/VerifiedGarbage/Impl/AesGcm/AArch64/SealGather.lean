module

public import VerifiedGarbage.Impl.AesGcm.AArch64

/-!
# AES-GCM one-shot encryption out of place, from a list of slices: AArch64 implementation

`vg_aes_gcm_seal_gather(ctx = x0, rounds = x1, nonce = x2, nonce_len = x3,
aad = x4, aad_len = x5, src = x6, src_count = x7, dst = [sp],
len = [sp + 8], tag = [sp + 16])`, generic over the implementation of
`vg_aes_gcm_seal` it calls (`f`): it copies the slices `src` lists, one
after the other, to `dst`, and encrypts them there in place with a call of
`vg_aes_gcm_seal(ctx, rounds, nonce, nonce_len, aad, aad_len, dst, len, tag)`.

It allocates a frame of 16 bytes: `tag`, the call's stack argument, at
`sp`, and our return address, which the call (`bl`) overwrites in `x30`, at
`sp + 8`; our stack arguments are then at `sp + 16` … `sp + 32`. Each slice
is copied, once its first 16 bytes have aligned where it goes to 16 bytes
(`alignHead`), 64 bytes at a time through `v0` … `v3` (`copyChunks`), then 16
bytes at a time through `v0` (`copyBlocks`), then its last `len mod 16`
bytes eight, then four, then one at a time (`copyW`), with
`x12` its address, `x13` its length and `x11` where it goes; `x6` and `x7`
step through the descriptors. Every register the copy writes is
caller-saved, and the branches are on `src_count` and the slices' lengths
alone.
-/

@[expose] public section

namespace VG.Impl.AesGcm.AArch64.SealGather

open VG.AArch64

/-- The frame's stack argument `tag` and our return address, and `dst` in
`x11`. -/
def entry : List Instr :=
  [.addSp .x16 0, .str .x .x30 .x16 8, .ldrSp .x17 32, .str .x .x17 .x16 0, .ldrSp .x11 16]

/-- Copies the `x14` (at least 1) blocks at `x12` to `x11`, through `v0`. -/
def copyBlocks : Prog isa :=
  .loop (.block [.ldrq .v0 .x12 0, .strq .v0 .x11 0, .addImm .x .x12 .x12 16,
    .addImm .x .x11 .x11 16, .subImm .x .x14 .x14 1]) (.nonzero .x .x14)

/-- The number of whole blocks of the slice, in `x14`. -/
def blocksArg : List Instr := [.lsr .x .x14 .x13 4]

/-- The number of its last bytes, in `x13`. -/
def bytesArg : List Instr := [.movz .x .x15 15 0, .logic .and .x .x13 .x13 .x15]

/-- Copies the `x13` (fewer than 64) bytes at `x12` to `x11`, advancing
`x11` past them. -/
def copySlice16 : Prog isa :=
  .seq (.block blocksArg)
  (.seq (.ite (.zero .x .x14) (.block []) copyBlocks)
  (.seq (.block bytesArg)
    (.ite (.zero .x .x13) (.block []) copyW)))

/-- Copies the `x14` (at least 1) chunks of 64 bytes at `x12` to `x11`,
through `v0` … `v3`, at offsets from the two pointers. -/
def copyChunks : Prog isa :=
  .loop (.block [.ldrq .v0 .x12 0, .strq .v0 .x11 0, .ldrq .v1 .x12 16, .strq .v1 .x11 16,
    .ldrq .v2 .x12 32, .strq .v2 .x11 32, .ldrq .v3 .x12 48, .strq .v3 .x11 48,
    .addImm .x .x12 .x12 64, .addImm .x .x11 .x11 64, .subImm .x .x14 .x14 1]) (.nonzero .x .x14)

/-- The number of whole chunks of 64 bytes of the slice, in `x14`. -/
def chunksArg : List Instr := [.lsr .x .x14 .x13 6]

/-- The number of its bytes after them, in `x13`. -/
def restArg : List Instr := [.movz .x .x15 63 0, .logic .and .x .x13 .x13 .x15]

/-- Copies the `x13` bytes at `x12` to `x11`, advancing `x11` past them: 64
bytes at a time, then as `copySlice16`. -/
def copySlice64 : Prog isa :=
  .seq (.block chunksArg)
  (.seq (.ite (.zero .x .x14) (.block []) copyChunks)
  (.seq (.block restArg) copySlice16))

/-- The first 16 bytes, through `v0`, and the pointers and the length moved
on by `16 - (x11 mod 16)` (1 to 16) bytes, so that `x11` is a multiple of 16:
the later stores do not cross cache lines. The bytes moved past and not yet
copied are copied again, the same. -/
def alignHead : List Instr :=
  [.ldrq .v0 .x12 0, .strq .v0 .x11 0, .movz .x .x15 15 0, .logic .and .x .x14 .x11 .x15,
    .movz .x .x15 16 0, .sub .x .x14 .x15 .x14, .add .x .x12 .x12 .x14, .add .x .x11 .x11 .x14,
    .sub .x .x13 .x13 .x14]

/-- Copies the `x13` bytes at `x12` to `x11`, advancing `x11` past them: if
there are at least 16, with `x11` aligned to 16 bytes after the first
(`alignHead`), as `copySlice64`; otherwise as `copySlice16`. -/
def copySlice : Prog isa :=
  .seq (.block blocksArg)
    (.ite (.zero .x .x14) copySlice16 (.seq (.block alignHead) copySlice64))

/-- The next descriptor: the slice's address in `x12` and length in `x13`. -/
def next : List Instr := [.ldr .x .x12 .x6 0, .ldr .x .x13 .x6 8, .addImm .x .x6 .x6 16]

/-- Copies the `x7` (at least 1) slices that the descriptors at `x6` list to
`x11`, one after the other. -/
def gatherLoop : Prog isa :=
  .loop (.seq (.block next) (.seq copySlice (.block [.subImm .x .x7 .x7 1]))) (.nonzero .x .x7)

/-- Copies the `x7` slices that the descriptors at `x6` list to `x11`. -/
def gather : Prog isa := .ite (.zero .x .x7) (.block []) gatherLoop

/-- `dst` and `len` as the call's `data` and `len`. -/
def callArgs : List Instr := [.ldrSp .x6 16, .ldrSp .x7 24]

/-- `vg_aes_gcm_seal_gather`, calling `f`, an implementation of `vg_aes_gcm_seal`. -/
def sealGather (f : Fn) : Prog isa :=
  .frame (.alloc 16)
    (.seq (.block entry)
    (.seq gather
    (.seq (.block callArgs)
    (.seq (.call f.name f.code)
      (.block [.ldrSp .x30 8])))))
    (.free 16)

/-! ## With the powers

`vg_aes_gcm_seal_gather_with_powers(…, dst = [sp], len = [sp + 8],
tag = [sp + 16], pw = [sp + 24])`, calling `f`, an implementation of
`vg_aes_gcm_seal_with_powers`: the same gathering, then
`vg_aes_gcm_seal_with_powers(ctx, rounds, nonce, nonce_len, aad, aad_len,
dst, len, tag, pw)`. Its frame of 32 bytes holds the call's stack arguments
`tag` and `pw` at `sp` and `sp + 8`, and our return address at `sp + 16`;
our stack arguments are then at `sp + 32` … `sp + 56`. -/

/-- The frame's stack arguments `tag` and `pw` and our return address, and
`dst` in `x11`. -/
def entryPw : List Instr :=
  [.addSp .x16 0, .str .x .x30 .x16 16, .ldrSp .x17 48, .str .x .x17 .x16 0, .ldrSp .x17 56,
    .str .x .x17 .x16 8, .ldrSp .x11 32]

/-- `dst` and `len` as the call's `data` and `len`. -/
def callArgsPw : List Instr := [.ldrSp .x6 32, .ldrSp .x7 40]

/-- `vg_aes_gcm_seal_gather_with_powers`, calling `f`, an implementation of
`vg_aes_gcm_seal_with_powers`. -/
def sealGatherPw (f : Fn) : Prog isa :=
  .frame (.alloc 32)
    (.seq (.block entryPw)
    (.seq gather
    (.seq (.block callArgsPw)
    (.seq (.call f.name f.code)
      (.block [.ldrSp .x30 16])))))
    (.free 32)

end VG.Impl.AesGcm.AArch64.SealGather
