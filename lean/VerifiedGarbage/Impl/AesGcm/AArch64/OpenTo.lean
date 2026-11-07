module

public import VerifiedGarbage.Impl.AesGcm.AArch64.SealGather

/-!
# AES-GCM decryption out of place, by a copy: AArch64 implementation

`openTo n f` takes the arguments `(ctx = x0, rounds = x1, nonce = x2,
nonce_len = x3, aad = x4, aad_len = x5, src = x6, len = x7, dst = [sp],
dst_len = [sp + 8], …)`, followed on the stack by the `n` stack arguments of
the function `f` it calls, an implementation of `vg_aes_gcm_open` or of one
of its instances (`tag = [sp + 16]`, `tag_len = [sp + 24]`, and for
`vg_aes_gcm_open_with_powers`, `pw = [sp + 32]`): it copies the `len` bytes
at `src` to `dst` (`SealGather.copySlice`, 16 bytes at a time through `v0`,
then the last `len mod 16` eight, four and one at a time), and decrypts them
there in place with a call of `f(ctx, rounds, nonce, nonce_len, aad,
aad_len, dst, len, …)`, with our stack arguments after `dst_len` as its own.
If it returns 0 (the tag is wrong), `dst` holds the ciphertext again, and is
zeroed a byte at a time (`wipe`); `x0` is left as the call left it, 0.

`vg_aes_gcm_open_to` is `openTo 2`, calling `vg_aes_gcm_open(ctx, rounds,
nonce, nonce_len, aad, aad_len, dst, len, tag, tag_len)`, and
`vg_aes_gcm_open_to_with_powers` is `openTo 3`, calling
`vg_aes_gcm_open_with_powers(…, tag, tag_len, pw)`.

It allocates a frame (`frameBytes n`, 32 bytes for both): the call's `n`
stack arguments at `sp`, `sp + 8`, …, and our return address, which the call
(`bl`) overwrites in `x30`, in the next doubleword, rounded up to 16 bytes;
our stack arguments are then just above it. Every register the copy and the
wipe write is caller-saved, and their branches are on `len` alone; the
branch after the call is on whether the tag is right.
-/

@[expose] public section

namespace VG.Impl.AesGcm.AArch64.OpenTo

open VG.AArch64
open VG.Impl.AesGcm.AArch64.SealGather (copySlice)

/-- The frame: the call's `n` stack arguments and our return address,
rounded up to 16 bytes. -/
def frameBytes (n : Nat) : Nat := (8 * n + 8 + 15) / 16 * 16

/-- Our stack argument `i + 2` (at `sp + F + 16 + 8 i`, with the frame of
`F` bytes allocated) as the call's stack argument `i` (at `sp + 8 i`), for
`i < n`, through `x17`; `x16` holds `sp`. -/
def copyArgs (F n : Nat) : List Instr :=
  (List.range n).flatMap fun i => [.ldrSp .x17 (F + 16 + 8 * i), .str .x .x17 .x16 (8 * i)]

/-- Our return address after the call's `n` stack arguments, those
arguments, and the copy's arguments: `dst` in `x11`, `src` in `x12` and
`len` in `x13`. -/
def entry (n : Nat) : List Instr :=
  [.addSp .x16 0, .str .x .x30 .x16 (8 * n)] ++ copyArgs (frameBytes n) n ++
    [.ldrSp .x11 (frameBytes n), .addImm .x .x12 .x6 0, .addImm .x .x13 .x7 0]

/-- `dst` as the call's `data`; `len` is still in `x7`. -/
def callArgs (n : Nat) : List Instr := [.ldrSp .x6 (frameBytes n)]

/-- `dst` in `x9`, `dst_len` (`len`) in `x10`, and zero in `x11`. -/
def wipeArgs (n : Nat) : List Instr :=
  [.ldrSp .x9 (frameBytes n), .ldrSp .x10 (frameBytes n + 8), .movz .x .x11 0 0]

/-- The `x10` bytes at `x9` zeroed, a byte at a time. -/
def wipeLoop : Prog isa :=
  .ite (.zero .x .x10) (.block [])
    (.loop (.block [.strb .x11 .x9 0, .addImm .x .x9 .x9 1, .subImm .x .x10 .x10 1])
      (.nonzero .x .x10))

/-- The `len` bytes at `dst` zeroed. -/
def wipe (n : Nat) : Prog isa := .seq (.block (wipeArgs n)) wipeLoop

/-- After the call: `dst` wiped if it returned 0. -/
def after (n : Nat) : Prog isa := .ite (.zero .w .x0) (wipe n) (.block [])

/-- Our return address back in `x30`. -/
def ret (n : Nat) : List Instr := [.ldrSp .x30 (8 * n)]

/-- `vg_aes_gcm_open_to` and its instances, calling `f`, an implementation of
`vg_aes_gcm_open` or of an instance of it with `n` stack arguments. -/
def openTo (n : Nat) (f : Fn) : Prog isa :=
  .frame (.alloc (frameBytes n))
    (.seq (.block (entry n))
    (.seq copySlice
    (.seq (.block (callArgs n))
    (.seq (.call f.name f.code)
    (.seq (after n)
      (.block (ret n)))))))
    (.free (frameBytes n))

end VG.Impl.AesGcm.AArch64.OpenTo
