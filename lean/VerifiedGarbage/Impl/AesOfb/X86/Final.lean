module

public import VerifiedGarbage.Impl.AesOfb.X86
public import VerifiedGarbage.Impl.AesCfb.X86.Final
public import VerifiedGarbage.Impl.Scrub.X86
public import VerifiedGarbage.Impl.StackScratch.X86

/-!
# AES-OFB of a message's last piece: x86 (32-bit) implementation

`cryptFinal b sfx` (cdecl: schedule, rounds, iv, data, len, scratch, save,
every argument on the stack): the code of `vg_aes_ofb_final`, whose
registration frames it with a buffer of its own on the stack, `save`, the
seventh argument, where the code keeps its caller's callee-saved registers.
It is AES-CFB's final function (`Impl.AesCfb.X86.final`) around a call of
the whole-block AES-OFB function of the same implementation of the block
functions (`b`, whose callers' names end in `sfx`, e.g. `_aesni`):

1. our caller's `ebx`, `esi`, `edi` and `ebp` saved in `save`;
2. a call of `vg_aes_ofb`'s code (`vg_aes_ofb_core`, and its variants,
   `Impl/AesOfb/X86.lean`) on the
   `len / 16` whole blocks, which leaves the last output block `Oₙ` in `iv`;
3. if `u = len mod 16 ≠ 0`, a call of the block function on the block at
   `iv` in place, which leaves `Oₙ₊₁ = CIPH_K(Oₙ)` there, the last output
   block used, and its first `u` bytes XORed into the `u` bytes left, a
   byte at a time;
4. the registers restored.

Only the pointers, `rounds` and `len` can affect timing.
-/

@[expose] public section

namespace VG.Impl.AesOfb.X86

open VG.X86
open VG.Impl.Aes.X86 (Blocks)

/-- `vg_aes_ofb_final`, calling `vg_aes_ofb`'s code with the block function
`b`, whose callers' names end in `sfx`, as an internal function of its own,
`vg_aes_ofb<sfx>_core`: `vg_aes_ofb` may also clear what it leaves. -/
def cryptFinal (b : Blocks) (sfx : String) : Prog isa :=
  Impl.AesCfb.X86.final ("vg_aes_ofb" ++ sfx ++ "_core") (crypt b) b

end VG.Impl.AesOfb.X86

/-! ## The functions as emitted

Each function, then its cleanup (`Impl.Scrub.X86.scrubAll rb W`): the `W`
bytes of stack below `esp` that it and its callees use zeroed, and the
registers a callee may change cleared but the `rb` bits of the result, so
that it returns without secret residue. -/

namespace VG.Impl.AesOfb.X86.Fn

open VG.X86
open VG.Impl.Aes.X86 (Blocks)
open Impl.StackScratch.X86 (withStackScratchWiped)

/-- `vg_aes_ofb` over the block function `b`, as emitted. -/
def crypt (b : Blocks) : Prog isa := Impl.Scrub.X86.scrubAll 0 24 (Impl.AesOfb.X86.crypt b)

/-- `vg_aes_ofb_final` over `b`, of the variant `sfx`, as emitted. -/
def cryptFinal (b : Blocks) (sfx : String) : Prog isa :=
  Impl.Scrub.X86.scrubAll 0 100 (withStackScratchWiped 48 6 4 (Impl.AesOfb.X86.cryptFinal b sfx))

end VG.Impl.AesOfb.X86.Fn
