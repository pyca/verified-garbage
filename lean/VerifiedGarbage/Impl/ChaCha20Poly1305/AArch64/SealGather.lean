module

public import VerifiedGarbage.Impl.AesGcm.AArch64.SealGather

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices: AArch64 implementation

`vg_chacha20_poly1305_seal_gather(key = x0, nonce = x1, aad = x2,
aad_len = x3, src = x4, src_count = x5, dst = x6, len = x7, tag = [sp])`,
generic over the implementation of `vg_chacha20_poly1305_seal` it calls
(`name`, `code`): it copies the slices `src` lists, one after the other, to
`dst` (AES-GCM's `gather`, `Impl/AesGcm/AArch64/SealGather.lean`), and
encrypts them there in place with a call of
`vg_chacha20_poly1305_seal(key, nonce, aad, aad_len, dst, len, tag)`.

It allocates a frame of 16 bytes, which keeps our return address, which the
call (`bl`) overwrites in `x30`, at `sp + 8`; our stack argument `tag` is
then at `sp + 16`. `dst`, `len` and `tag` wait for the call in `x8`, `x9`
and `x10`, which the gathering does not write: it steps through the
descriptors with `x6` and `x7` and writes to `x11`.
-/

@[expose] public section

namespace VG.Impl.ChaCha20Poly1305.AArch64.SealGather

open VG.AArch64

/-- Our return address in the frame; `dst`, `len` and `tag` kept in `x8`,
`x9` and `x10`; and the gathering's arguments: the descriptors in `x6`, their
number in `x7` and `dst` in `x11`. -/
def entry : List Instr :=
  [.addSp .x16 0, .str .x .x30 .x16 8, .ldrSp .x10 16, .addImm .x .x8 .x6 0, .addImm .x .x9 .x7 0,
    .addImm .x .x11 .x6 0, .addImm .x .x6 .x4 0, .addImm .x .x7 .x5 0]

/-- `dst`, `len` and `tag` as the call's `data`, `len` and `tag`. -/
def callArgs : List Instr := [.addImm .x .x4 .x8 0, .addImm .x .x5 .x9 0, .addImm .x .x6 .x10 0]

/-- `vg_chacha20_poly1305_seal_gather`, calling `code`, an implementation of
`vg_chacha20_poly1305_seal`, as `name`. -/
def sealGather (name : String) (code : Prog isa) : Prog isa :=
  .frame (.alloc 16)
    (.seq (.block entry)
    (.seq AesGcm.AArch64.SealGather.gather
    (.seq (.block callArgs)
    (.seq (.call name code)
      (.block [.ldrSp .x30 8])))))
    (.free 16)

end VG.Impl.ChaCha20Poly1305.AArch64.SealGather
