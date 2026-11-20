module

public import VerifiedGarbage.Impl.AesOfb.AArch64
public import VerifiedGarbage.Impl.AesCfb.AArch64.Final
public import VerifiedGarbage.Impl.Residue.AArch64.Union
public import VerifiedGarbage.Impl.StackScratch.AArch64

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

/-- `vg_aes_ofb_final`, calling `vg_aes_ofb`'s code with the block function
`b`, whose callers' names end in `sfx`, as an internal function of its own,
`vg_aes_ofb<sfx>_core`: `vg_aes_ofb` also clears the registers it leaves. -/
def cryptFinal (b : Blocks) (sfx : String) : Prog isa :=
  Impl.AesCfb.AArch64.final ("vg_aes_ofb" ++ sfx ++ "_core") (crypt b) b

/-! ## The functions, as emitted

Each function is its code, then its cleanup
(`Impl.Residue.AArch64.scrubAll`): the registers it writes that the calling
convention does not preserve are cleared, and the stack it uses is zeroed,
so that it returns without secret residue. The registers are those its own
instructions write, stated here, and those the block function it calls
states it writes (`b.clear`). -/

namespace Fn

open VG.Impl.Residue.AArch64 (Clear scrubAll)

/-- The registers `vg_aes_ofb`'s own instructions write. -/
def cryptOwn : Clear := ⟨[.x1, .x2, .x3, .x4, .x9, .x10, .x16, .x17], [], []⟩

/-- `vg_aes_ofb`: `crypt`, its registers cleared; it uses no stack. -/
def crypt (b : Blocks) : Prog isa :=
  scrubAll 0 0 (cryptOwn.union b.clear) (AesOfb.AArch64.crypt b)

/-- The registers `vg_aes_ofb_final`'s own instructions write. -/
def cryptFinalOwn : Clear := ⟨[.x1, .x2, .x3, .x4, .x6, .x7, .x9, .x10, .x16, .x17], [], []⟩

/-- `vg_aes_ofb_final`: `cryptFinal` with `save` in its frame, its registers
cleared and its 64 bytes of stack zeroed. -/
def cryptFinal (b : Blocks) (sfx : String) : Prog isa :=
  scrubAll 64 0 (cryptFinalOwn.union b.clear)
    (Impl.StackScratch.AArch64.withStackScratchWiped 64 .x6 8 (AesOfb.AArch64.cryptFinal b sfx))

end Fn

end VG.Impl.AesOfb.AArch64
