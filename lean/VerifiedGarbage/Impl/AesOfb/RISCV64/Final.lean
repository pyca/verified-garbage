module

public import VerifiedGarbage.Impl.AesOfb.RISCV64
public import VerifiedGarbage.Impl.AesCfb.RISCV64.Final

/-!
# AES-OFB of a message's last piece: RISC-V implementation

`cryptFinal` (schedule = a0, rounds = a1, iv = a2, data = a3, len = a4,
scratch = a5, save = a6): the code of `vg_aes_ofb_final`, whose
registration frames it with a buffer of its own on the stack, `save`, the
seventh argument, where the code keeps its return address and its caller's
callee-saved registers. It is AES-CFB's final function
(`Impl.AesCfb.RISCV64.final`) around a call of the whole-block AES-OFB
function, `vg_aes_ofb` (`Impl/AesOfb/RISCV64.lean`):

1. the return address and the registers saved in `save`, and the arguments
   kept in callee-saved registers;
2. a call of `vg_aes_ofb` on the `len / 16` whole blocks, which leaves the
   last output block `Oₙ` in `iv`;
3. if `u = len mod 16 ≠ 0`, a call of the block function
   `vg_aes_encrypt_blocks` on the block at `iv` in place, which leaves
   `Oₙ₊₁ = CIPH_K(Oₙ)` there, the last output block used, and its first `u`
   bytes XORed into the `u` bytes left, a byte at a time;
4. the registers restored.

Only the pointers, `rounds` and `len` can affect timing.
-/

@[expose] public section

namespace VG.Impl.AesOfb.RISCV64

open VG.RISCV64

/-- `vg_aes_ofb_final`, calling `vg_aes_ofb`. -/
def cryptFinal : Prog isa := Impl.AesCfb.RISCV64.final "vg_aes_ofb" crypt

end VG.Impl.AesOfb.RISCV64
