module

public import VerifiedGarbage.Impl.AesOfb.X86_64
public import VerifiedGarbage.Impl.AesCfb.X86_64.Final

/-!
# AES-OFB of a message's last piece: x86-64 implementation

`cryptFinal b sfx` (schedule = rdi, rounds = rsi, iv = rdx, data = rcx,
len = r8, scratch = r9, save = `[rsp + 8]`): the code of `vg_aes_ofb_final`,
whose registration frames it with a buffer of its own on the stack, `save`,
the seventh argument, where the code keeps its caller's callee-saved
registers. It is AES-CFB's final function (`Impl.AesCfb.X86_64.final`)
around a call of the whole-block AES-OFB function of the same
implementation of the block functions (`b`, whose callers' names end in
`sfx`, e.g. `_aesni`):

1. the registers saved in `save`, and the arguments kept in callee-saved
   registers;
2. a call of `vg_aes_ofb` (and its variants, `Impl/AesOfb/X86_64.lean`) on
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

namespace VG.Impl.AesOfb.X86_64

open VG.X86_64
open VG.Impl.Aes.X86_64 (Blocks)

/-- `vg_aes_ofb_final`, calling `vg_aes_ofb` with the block function `b`,
whose callers' names end in `sfx`. -/
def cryptFinal (b : Blocks) (sfx : String) : Prog isa :=
  Impl.AesCfb.X86_64.final ("vg_aes_ofb" ++ sfx) (crypt b) b

end VG.Impl.AesOfb.X86_64
