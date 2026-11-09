module

public import VerifiedGarbage.Impl.AesOfb.Arm
public import VerifiedGarbage.Impl.AesCfb.Arm.Final

/-!
# AES-OFB of a message's last piece: 32-bit ARM implementation

`cryptFinal` (schedule = r0, rounds = r1, iv = r2, data = r3, len = `[sp]`,
scratch = `[sp + 4]`, save = `[sp + 8]`): the code of `vg_aes_ofb_final`,
whose registration frames it with a buffer of its own on the stack, `save`,
the seventh argument, where the code keeps its caller's callee-saved
registers and its return address. It is AES-CFB's final function
(`Impl.AesCfb.Arm.final`) around a call of the whole-block AES-OFB function:

1. the registers saved in `save`, and the arguments kept in callee-saved
   registers;
2. a call of `vg_aes_ofb` (`Impl/AesOfb/Arm.lean`) on the `len / 16` whole
   blocks, which leaves the last output block `Oₙ` in `iv`;
3. if `u = len mod 16 ≠ 0`, a call of `vg_aes_encrypt_blocks` on the block
   at `iv` in place, which leaves `Oₙ₊₁ = CIPH_K(Oₙ)` there, the last output
   block used, and its first `u` bytes XORed into the `u` bytes left, a byte
   at a time;
4. the registers restored.

Only the pointers, `rounds` and `len` can affect timing.
-/

@[expose] public section

namespace VG.Impl.AesOfb.Arm

open VG.Arm

/-- `vg_aes_ofb_final`, calling `vg_aes_ofb`. -/
def cryptFinal : Prog isa := Impl.AesCfb.Arm.final "vg_aes_ofb" crypt

end VG.Impl.AesOfb.Arm
