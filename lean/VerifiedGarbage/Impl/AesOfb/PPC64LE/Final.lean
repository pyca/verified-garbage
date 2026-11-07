module

public import VerifiedGarbage.Impl.AesOfb.PPC64LE
public import VerifiedGarbage.Impl.AesCfb.PPC64LE.Final

/-!
# AES-OFB of a message's last piece: PPC64LE implementation

`cryptFinal` (schedule = r3, rounds = r4, iv = r5, data = r6, len = r7,
scratch = r8, save = r9): the code of `vg_aes_ofb_final`, whose registration
frames it with a buffer of its own on the stack, `save`, the seventh
argument, where the code keeps its return address and its caller's
callee-saved registers. It is AES-CFB's final function
(`Impl.AesCfb.PPC64LE.final`) around a call of the whole-block AES-OFB
function `vg_aes_ofb` (`Impl/AesOfb/PPC64LE.lean`):

1. the return address and the registers saved in `save`, and the arguments
   kept in callee-saved registers;
2. a call of `vg_aes_ofb` on the `len / 16` whole blocks, which leaves the
   last output block `Oₙ` in `iv`;
3. if `u = len mod 16 ≠ 0`, a call of the block function on the block at
   `iv` in place, which leaves `Oₙ₊₁ = CIPH_K(Oₙ)` there, the last output
   block used, and its first `u` bytes XORed into the `u` bytes left, a
   byte at a time;
4. the registers and the return address restored.

Only the pointers, `rounds` and `len` can affect timing.
-/

@[expose] public section

namespace VG.Impl.AesOfb.PPC64LE

open VG.PPC64LE

/-- `vg_aes_ofb_final`, calling `vg_aes_ofb`. -/
def cryptFinal : Prog isa := Impl.AesCfb.PPC64LE.final "vg_aes_ofb" crypt

end VG.Impl.AesOfb.PPC64LE
