module

public import VerifiedGarbage.Impl.AesGcm.Arm.SealGather

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices: 32-bit ARM implementation

`vg_chacha20_poly1305_seal_gather(key = r0, nonce = r1, aad = r2,
aad_len = r3, src = [sp], src_count = [sp + 4], dst = [sp + 8],
len = [sp + 12], tag = [sp + 16])` copies the slices `src` lists, one after
the other, to `dst` (AES-GCM's `gather`, `Impl/AesGcm/Arm/SealGather.lean`),
and encrypts them there in place with a call of
`vg_chacha20_poly1305_seal(key, nonce, aad, aad_len, dst, len, tag)`
(`seal`, its symbol and code).

It allocates a frame of 32 bytes: the call's three stack arguments at `sp`
… `sp + 8`, our return address, which the call (`bl`) overwrites in `lr`,
at `sp + 12`, and `r0`–`r3`, which the copy uses, at `sp + 16` …
`sp + 28`; our stack arguments are then at `sp + 32` … `sp + 48`. The frame
and the arguments are reached through `r12`, set to `sp` before each use
(`setFp`).
-/

@[expose] public section

namespace VG.Impl.ChaCha20Poly1305.Arm.SealGather

open VG.Arm
open VG.Impl.AesGcm.Arm.SealGather (setFp)

/-- Our return address and `r0`–`r3` kept in the frame; the call's stack
arguments `dst`, `len` and `tag` laid out in it; and the copy's registers:
`src` in `r0`, `dst` in `r2` and `src_count` in `lr`. -/
def entryWords : List Instr :=
  [.str .lr .r12 12, .str .r0 .r12 16, .str .r1 .r12 20, .str .r2 .r12 24, .str .r3 .r12 28,
    .ldr .lr .r12 40, .str .lr .r12 0, .ldr .lr .r12 44, .str .lr .r12 4, .ldr .lr .r12 48, .str .lr .r12 8,
    .ldr .r0 .r12 32, .ldr .r2 .r12 40, .ldr .lr .r12 36]

def entry : Prog isa := .seq (.block setFp) (.block entryWords)

/-- `r0`–`r3` back from the frame. -/
def argWords : List Instr := [.ldr .r0 .r12 16, .ldr .r1 .r12 20, .ldr .r2 .r12 24, .ldr .r3 .r12 28]

def callArgs : Prog isa := .seq (.block setFp) (.block argWords)

/-- Our return address back from the frame. -/
def ret : Prog isa := .seq (.block setFp) (.block [.ldr .lr .r12 12])

/-- `vg_chacha20_poly1305_seal_gather`, calling `vg_chacha20_poly1305_seal`
(`name`, `code`). -/
def sealGather (name : String) (code : Prog isa) : Prog isa :=
  .frame (.alloc 32)
    (.seq entry
    (.seq AesGcm.Arm.SealGather.gather
    (.seq callArgs
    (.seq (.call name code) ret))))
    (.free 32)

end VG.Impl.ChaCha20Poly1305.Arm.SealGather
