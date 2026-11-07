module

public import VerifiedGarbage.Impl.AesGcm.Arm.SealGather

/-!
# AES-GCM decryption out of place, by a copy: 32-bit ARM implementation

`vg_aes_gcm_open_to(ctx = r0, rounds = r1, nonce = r2, nonce_len = r3,
aad = [sp], aad_len = [sp + 4], src = [sp + 8], len = [sp + 12],
dst = [sp + 16], dst_len = [sp + 20], tag = [sp + 24], tag_len = [sp + 28])`,
generic over the implementation of `vg_aes_gcm_open` it calls (`name`,
`code`): it copies the `len` bytes at `src` to `dst`
(`SealGather.copySlice`, whose descriptor, the address and the length of the
slice, is our stack arguments `src` and `len`, which are adjacent), and
decrypts them there in place with a call of
`vg_aes_gcm_open(ctx, rounds, nonce, nonce_len, aad, aad_len, dst, len, tag, tag_len)`.
If it returns 0 (the tag is wrong), `dst` holds the ciphertext again, and is
zeroed a byte at a time (`wipe`); `r0` is left as the call left it, 0.

It allocates a frame of 48 bytes: the call's six stack arguments at `sp` …
`sp + 20`, our return address, which the call (`bl`) overwrites in `lr`, at
`sp + 24`, and `r0`–`r3`, which the copy uses, at `sp + 28` … `sp + 40`
(`sp + 44` is unused, for the frame's alignment); our stack arguments are
then at `sp + 48` … `sp + 76`. The frame and the arguments are reached
through `r12`, set to `sp` before each use (`SealGather.setFp`). Every
register the function writes is caller-saved, and the branches are on `len`
alone, but the one after the call, on whether the tag is right.
-/

@[expose] public section

namespace VG.Impl.AesGcm.Arm.OpenTo

open VG.Arm
open VG.Impl.AesGcm.Arm.SealGather (setFp copySlice)

/-- Our return address and `r0`–`r3` kept in the frame; the call's stack
arguments `aad`, `aad_len`, `dst`, `len`, `tag` and `tag_len` laid out in
it; and the copy's registers: the address of our argument `src` (followed
by `len`) in `r0` and `dst` in `r2`. -/
def entryWords : List Instr :=
  [.str .lr .r12 24, .str .r0 .r12 28, .str .r1 .r12 32, .str .r2 .r12 36, .str .r3 .r12 40,
    .ldr .lr .r12 48, .str .lr .r12 0, .ldr .lr .r12 52, .str .lr .r12 4, .ldr .lr .r12 64, .str .lr .r12 8,
    .ldr .lr .r12 60, .str .lr .r12 12, .ldr .lr .r12 72, .str .lr .r12 16, .ldr .lr .r12 76, .str .lr .r12 20,
    addI .r0 .r12 56, .ldr .r2 .r12 64]

def entry : Prog isa := .seq (.block setFp) (.block entryWords)

/-- `r0`–`r3` back from the frame. -/
def argWords : List Instr := [.ldr .r0 .r12 28, .ldr .r1 .r12 32, .ldr .r2 .r12 36, .ldr .r3 .r12 40]

def callArgs : Prog isa := .seq (.block setFp) (.block argWords)

/-- `dst` in `r1`, `len` in `r2`, and zero in `r3`. -/
def wipeArgs : List Instr := [.ldr .r1 .r12 64, .ldr .r2 .r12 60, .mov .r3 (imm 0)]

/-- The `r2` bytes at `r1` zeroed, a byte at a time. -/
def wipeLoop : Prog isa :=
  .seq (.block [.cmp .r2 (imm 0)])
    (.ite .eq (.block []) (.loop (.block [.strb .r3 .r1 0, addI .r1 .r1 1, .subs .r2 .r2 (imm 1)]) .ne))

/-- The `len` bytes at `dst` zeroed. -/
def wipe : Prog isa := .seq (.seq (.block setFp) (.block wipeArgs)) wipeLoop

/-- After the call: `dst` wiped if it returned 0. -/
def after : Prog isa := .seq (.block [.cmp .r0 (imm 0)]) (.ite .eq wipe (.block []))

/-- Our return address back from the frame. -/
def ret : Prog isa := .seq (.block setFp) (.block [.ldr .lr .r12 24])

/-- `vg_aes_gcm_open_to`, calling `vg_aes_gcm_open` (`name`, `code`). -/
def openTo (name : String) (code : Prog isa) : Prog isa :=
  .frame (.alloc 48)
    (.seq entry
    (.seq copySlice
    (.seq callArgs
    (.seq (.call name code)
    (.seq after ret)))))
    (.free 48)

end VG.Impl.AesGcm.Arm.OpenTo
