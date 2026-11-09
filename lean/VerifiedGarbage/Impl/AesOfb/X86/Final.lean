module

public import VerifiedGarbage.Impl.AesOfb.X86
public import VerifiedGarbage.Impl.AesCfb.X86.Final

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
2. a call of `vg_aes_ofb` (and its variants, `Impl/AesOfb/X86.lean`) on the
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

/-- `vg_aes_ofb_final`, calling `vg_aes_ofb` with the block function `b`,
whose callers' names end in `sfx`. -/
def cryptFinal (b : Blocks) (sfx : String) : Prog isa :=
  Impl.AesCfb.X86.final ("vg_aes_ofb" ++ sfx) (crypt b) b

end VG.Impl.AesOfb.X86
