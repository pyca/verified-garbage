module

public import VerifiedGarbage.Impl.AesGcm.AArch64.SealGather
public import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64.Stitched
public import VerifiedGarbage.Impl.Scrub.AArch64.Union
public import VerifiedGarbage.Impl.StackScratch.AArch64

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

/-! ## The functions, as emitted

Each function is its code in its frame, then its cleanup
(`Impl.Scrub.AArch64.scrubAll`): the registers it writes that the calling
convention does not preserve are cleared, but the 32 bits of `open`'s and
`open_to`'s result, and the stack it uses is zeroed, so that it returns without secret residue. The
registers are those its own instructions write, stated here, and those the
stream it calls states it writes (`XorCallee.clear`). -/

namespace VG.Impl.ChaCha20Poly1305.AArch64.Fn

open VG.AArch64
open VG.Impl.ChaCha20.AArch64 (XorCallee)
open VG.Impl.Scrub.AArch64 (Clear scrubAll)
open VG.Impl.StackScratch.AArch64 (withStackScratchWiped withStackArgScratchWiped)

/-- The registers `seal` and `seal_gather` write themselves. -/
def sealOwn : Clear :=
  ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
   [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24,
    .v25, .v26, .v27, .v30, .v31],
   []⟩

/-- The registers `open` and `open_to` write themselves. -/
def openOwn : Clear :=
  ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
   [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24,
    .v25, .v26, .v27, .v28, .v29, .v30, .v31],
   [.v8, .v9]⟩

/-- `seal`'s code in its frame of 1280 bytes, 96 words of them its working
space. -/
def sealBody (c : XorCallee) (stitched : Bool) : Prog isa :=
  withStackScratchWiped 1280 .x7 96 (sealCode c stitched)

/-- `open`'s code in its frame of 1312 bytes. -/
def openBody (c : XorCallee) (stitched : Bool) : Prog isa :=
  withStackScratchWiped 1312 .x7 96 (openInPlace c stitched)

/-- `open_to`'s code in its frame of 1328 bytes, its last two arguments on
the stack. -/
def openToBody (c : XorCallee) (stitched : Bool) : Prog isa :=
  withStackArgScratchWiped 1328 1 96 (openTo c stitched)

/-- `vg_chacha20_poly1305_seal`, with the stream `c`, the data absorbed
inside the eight-block kernel if `stitched`. -/
def sealWhole (c : XorCallee) (stitched : Bool) : Prog isa :=
  scrubAll 1280 0 (sealOwn.union c.clear) (sealBody c stitched)

/-- `vg_chacha20_poly1305_open`. -/
def openZero (c : XorCallee) (stitched : Bool) : Prog isa :=
  scrubAll 1312 32 (openOwn.union c.clear) (openBody c stitched)

/-- `vg_chacha20_poly1305_open_to`. -/
def openTo (c : XorCallee) (stitched : Bool) : Prog isa :=
  scrubAll 1328 32 (openOwn.union c.clear) (openToBody c stitched)

/-- `seal_gather`'s code: the gathering, then a call of `seal`
(`sealWhole`), the exported function with the same stream. -/
def sealGatherBody (c : XorCallee) (stitched : Bool) : Prog isa :=
  SealGather.sealGather ("vg_chacha20_poly1305_seal" ++ c.suffix) (sealWhole c stitched)

/-- `vg_chacha20_poly1305_seal_gather`. -/
def sealGather (c : XorCallee) (stitched : Bool) : Prog isa :=
  scrubAll 1296 0 (sealOwn.union c.clear) (sealGatherBody c stitched)

end VG.Impl.ChaCha20Poly1305.AArch64.Fn
