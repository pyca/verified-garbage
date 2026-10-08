import VerifiedGarbage.Impl.AesGcm.AArch64

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
is copied 16 bytes at a time through `v0` (`copyBlocks`), then its last
`len mod 16` bytes one at a time (`copyLoop`), with `x12` its address, `x13`
its length and `x11` where it goes; `x6` and `x7` step through the
descriptors. Every register the copy writes is caller-saved, and the
branches are on `src_count` and the slices' lengths alone.
-/

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

/-- Copies the `x13` bytes at `x12` to `x11`, advancing `x11` past them. -/
def copySlice : Prog isa :=
  .seq (.block blocksArg)
  (.seq (.ite (.zero .x .x14) (.block []) copyBlocks)
  (.seq (.block bytesArg)
    (.ite (.zero .x .x13) (.block []) copyLoop)))

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

end VG.Impl.AesGcm.AArch64.SealGather
