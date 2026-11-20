module

public import VerifiedGarbage.Impl.AesGcm.X86.SealGather
public import VerifiedGarbage.Impl.ChaCha20Poly1305.X86
public import VerifiedGarbage.Impl.Scrub.X86
public import VerifiedGarbage.Impl.StackScratch.X86

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

@[expose] public section

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

/-! ## The functions as emitted

Each function, in its frame, then its cleanup (`Impl.Scrub.X86.scrubF rb W`):
the `W` bytes of stack below `esp` that its frame and its calls use zeroed,
and the registers a callee may change cleared but the 32 bits of `open`'s and
`open_to`'s result, so that it returns without secret residue. `seal_gather`
calls `seal`'s code in its frame as the internal
`vg_chacha20_poly1305_seal_core` (with the implementation's suffix), since the
exported `seal` is followed by its cleanup. -/

namespace VG.Impl.ChaCha20Poly1305.X86.Fn

open VG.X86
open VG.Impl.ChaCha20.X86 (Callee)
open VG.Impl.StackScratch.X86 (withStackScratchWiped)

/-- `vg_chacha20_poly1305_seal`, calling the implementation `c` of `vg_chacha20_xor`, as emitted. -/
def «seal» (c : Callee) : Prog isa :=
  Impl.Scrub.X86.scrubF 0 1280 (withStackScratchWiped 740 7 176 (Impl.ChaCha20Poly1305.X86.«seal» c))

/-- `vg_chacha20_poly1305_open`, as emitted. -/
def «open» (c : Callee) : Prog isa :=
  Impl.Scrub.X86.scrubF 32 1280 (withStackScratchWiped 740 7 176 (Impl.ChaCha20Poly1305.X86.«open» c))

/-- `vg_chacha20_poly1305_open_to`, as emitted. -/
def openTo (c : Callee) : Prog isa :=
  Impl.Scrub.X86.scrubF 32 1288 (withStackScratchWiped 748 9 176 (Impl.ChaCha20Poly1305.X86.openTo c))

/-- `vg_chacha20_poly1305_seal_gather`, calling `seal`'s code in its frame as
`vg_chacha20_poly1305_seal_core` with the suffix `sfx` of `c`, as emitted. -/
def sealGather (c : Callee) (sfx : String) : Prog isa :=
  Impl.Scrub.X86.scrubF 0 1332 (SealGather.sealGather ("vg_chacha20_poly1305_seal_core" ++ sfx)
    (withStackScratchWiped 740 7 176 (Impl.ChaCha20Poly1305.X86.«seal» c)))

end VG.Impl.ChaCha20Poly1305.X86.Fn
