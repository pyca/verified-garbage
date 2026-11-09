module

public import VerifiedGarbage.Impl.AesOfb.AArch64
public import VerifiedGarbage.Impl.AesCfb.AArch64.Final

/-!
# AES-OFB of a message's last piece: AArch64 implementation

`cryptFinal b sfx` (schedule = x0, rounds = x1, iv = x2, data = x3,
len = x4, scratch = x5, save = x6): the code of `vg_aes_ofb_final`, whose
registration frames it with a buffer of its own on the stack, `save`, the
seventh argument, where the code keeps its caller's callee-saved registers
and its return address. It is AES-CFB's final function
(`Impl.AesCfb.AArch64.final`) around a call of the whole-block AES-OFB
function of the same implementation of the block functions (`b`, whose
callers' names end in `sfx`, e.g. `_aes`):

1. the registers saved in `save`, and the arguments kept in callee-saved
   registers;
2. a call of `vg_aes_ofb` (and its variants, `Impl/AesOfb/AArch64.lean`) on
   the `len / 16` whole blocks, which leaves the last output block `Oₙ` in
   `iv`;
3. if `u = len mod 16 ≠ 0`, a call of the block function on the block at
   `iv` in place, which leaves `Oₙ₊₁ = CIPH_K(Oₙ)` there, the last output
   block used, and its first `u` bytes XORed into the `u` bytes left, a
   byte at a time;
4. the registers restored.

Only the pointers, `rounds` and `len` can affect timing.
-/

@[expose] public section

namespace VG.Impl.AesOfb.AArch64

open VG.AArch64
open VG.Impl.Aes.AArch64 (Blocks)

/-- `vg_aes_ofb_final`, calling `vg_aes_ofb` with the block function `b`,
whose callers' names end in `sfx`. -/
def cryptFinal (b : Blocks) (sfx : String) : Prog isa :=
  Impl.AesCfb.AArch64.final ("vg_aes_ofb" ++ sfx) (crypt b) b

end VG.Impl.AesOfb.AArch64
