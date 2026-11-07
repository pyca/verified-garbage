module

public import VerifiedGarbage.Impl.AesGcm.X86.SealGather

/-!
# AES-GCM decryption out of place, by a copy: x86 (32-bit) implementation

`vg_aes_gcm_open_to(ctx, rounds, nonce, nonce_len, aad, aad_len, src, len,
dst, dst_len, tag, tag_len)`, cdecl (every argument on the stack, at
`[esp + 4]` on entry), generic over the implementation of `vg_aes_gcm_open`
it calls (`name`, `code`): it copies the `len` bytes at `src` to `dst`
(`SealGather.copySlice`, whose descriptor, the address and the length of the
slice, is our arguments `src` and `len`, which are adjacent), and decrypts
them there in place with a call of
`vg_aes_gcm_open(ctx, rounds, nonce, nonce_len, aad, aad_len, dst, len, tag, tag_len)`.
If it returns 0 (the tag is wrong), `dst` holds the ciphertext again, and is
zeroed a byte at a time (`wipe`); `eax` is then 0 again.

It allocates a frame of 48 bytes: the call's ten arguments at `esp` …
`esp + 36`, and our caller's `esi` and `edi`, which the copy uses, at
`esp + 40` and `esp + 44`; our arguments are then at `esp + 52` …
`esp + 96`. The copy has `esi` at our argument `src` and `edx` at `dst`. The
branches are on `len` alone, but the one after the call, on whether the tag
is right.
-/

@[expose] public section

namespace VG.Impl.AesGcm.X86.OpenTo

open VG.X86
open VG.Impl.AesGcm.X86.SealGather (sp copySlice)

/-- Our caller's `esi` and `edi` kept in the frame; the call's arguments
`ctx`, `rounds`, `nonce`, `nonce_len`, `aad`, `aad_len`, `dst`, `len`, `tag`
and `tag_len` laid out in it; and the copy's registers: the address of our
argument `src` (followed by `len`) in `esi` and `dst` in `edx`. -/
def entry : List Instr :=
  [.store (sp 40) .esi, .store (sp 44) .edi,
    .mov .eax (.mem (sp 52)), .store (sp 0) .eax, .mov .eax (.mem (sp 56)), .store (sp 4) .eax,
    .mov .eax (.mem (sp 60)), .store (sp 8) .eax, .mov .eax (.mem (sp 64)), .store (sp 12) .eax,
    .mov .eax (.mem (sp 68)), .store (sp 16) .eax, .mov .eax (.mem (sp 72)), .store (sp 20) .eax,
    .mov .eax (.mem (sp 84)), .store (sp 24) .eax, .mov .eax (.mem (sp 80)), .store (sp 28) .eax,
    .mov .eax (.mem (sp 92)), .store (sp 32) .eax, .mov .eax (.mem (sp 96)), .store (sp 36) .eax,
    .mov .esi (.reg .esp), .alu .add .esi (imm 76), .mov .edx (.mem (sp 84))]

/-- `dst` in `edx`, `len` in `ecx`, and zero in `eax`. -/
def wipeArgs : List Instr := [.mov .edx (.mem (sp 84)), .mov .ecx (.mem (sp 80)), .mov .eax (imm 0)]

/-- The `ecx` bytes at `edx` zeroed, a byte at a time. -/
def wipeLoop : Prog isa :=
  .seq (.block [.alu .cmp .ecx (imm 0)])
    (.ite .e (.block [])
      (.loop (.block [.store8 (at_ .edx 0) .al, .alu .add .edx (imm 1), .alu .sub .ecx (imm 1)]) .ne))

/-- The `len` bytes at `dst` zeroed. -/
def wipe : Prog isa := .seq (.block wipeArgs) wipeLoop

/-- After the call: `dst` wiped if it returned 0. -/
def after : Prog isa := .seq (.block [.alu .test .eax (.reg .eax)]) (.ite .e wipe (.block []))

/-- Our caller's `esi` and `edi` back from the frame. -/
def restore : List Instr := [.mov .esi (.mem (sp 40)), .mov .edi (.mem (sp 44))]

/-- `vg_aes_gcm_open_to`, calling `vg_aes_gcm_open` (`name`, `code`). -/
def openTo (name : String) (code : Prog isa) : Prog isa :=
  .frame (.alloc 48)
    (.seq (.block entry)
    (.seq copySlice
    (.seq (.call name code)
    (.seq after
      (.block restore)))))
    (.free 48)

end VG.Impl.AesGcm.X86.OpenTo
