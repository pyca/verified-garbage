import VerifiedGarbage.Impl.AesGcm.X86.SealGather

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices: x86 (32-bit) implementation

`vg_chacha20_poly1305_seal_gather(key, nonce, aad, aad_len, src, src_count,
dst, len, tag)`, cdecl (every argument on the stack, at `[esp + 4]` on
entry), copies the slices `src` lists, one after the other, to `dst`
(AES-GCM's `gather`, `Impl/AesGcm/X86/SealGather.lean`), and encrypts them
there in place with a call of
`vg_chacha20_poly1305_seal(key, nonce, aad, aad_len, dst, len, tag)`
(`name`, `code`: an instance of it).

It allocates a frame of 48 bytes: the call's seven arguments at `esp` …
`esp + 24`, and our caller's `ebx`, `esi` and `edi`, which the copy uses, at
`esp + 36` … `esp + 44`; our arguments are then at `esp + 52` … `esp + 84`.
-/

namespace VG.Impl.ChaCha20Poly1305.X86.SealGather

open VG.X86
open VG.Impl.AesGcm.X86.SealGather (sp)

/-- Our caller's `ebx`, `esi` and `edi` kept in the frame; the call's
arguments `key`, `nonce`, `aad`, `aad_len`, `dst`, `len` and `tag` laid out
in it; and the copy's registers: `src` in `esi`, `src_count` in `ebx` and
`dst` in `edx`. -/
def entry : List Instr :=
  [.store (sp 36) .ebx, .store (sp 40) .esi, .store (sp 44) .edi,
    .mov .eax (.mem (sp 52)), .store (sp 0) .eax, .mov .eax (.mem (sp 56)), .store (sp 4) .eax,
    .mov .eax (.mem (sp 60)), .store (sp 8) .eax, .mov .eax (.mem (sp 64)), .store (sp 12) .eax,
    .mov .eax (.mem (sp 76)), .store (sp 16) .eax, .mov .eax (.mem (sp 80)), .store (sp 20) .eax,
    .mov .eax (.mem (sp 84)), .store (sp 24) .eax,
    .mov .esi (.mem (sp 68)), .mov .ebx (.mem (sp 72)), .mov .edx (.mem (sp 76))]

/-- `vg_chacha20_poly1305_seal_gather`, calling `vg_chacha20_poly1305_seal`
(`name`, `code`). -/
def sealGather (name : String) (code : Prog isa) : Prog isa :=
  .frame (.alloc 48)
    (.seq (.block entry)
    (.seq AesGcm.X86.SealGather.gather
    (.seq (.call name code)
      (.block AesGcm.X86.SealGather.restore))))
    (.free 48)

end VG.Impl.ChaCha20Poly1305.X86.SealGather
