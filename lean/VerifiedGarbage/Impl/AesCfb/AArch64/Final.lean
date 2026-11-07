module

public import VerifiedGarbage.Impl.AesCfb.AArch64
public import VerifiedGarbage.Impl.Modes.AArch64.FbFinal

/-!
# AES-CFB128 of a message's last piece: AArch64 implementation

`final name whole b` (schedule = x0, rounds = x1, iv = x2, data = x3,
len = x4, scratch = x5, save = x6): the code of `vg_aes_cfb128_encrypt_final`
and `vg_aes_cfb128_decrypt_final`, whose registrations frame it with a
buffer of their own on the stack, `save`, the seventh argument, where the
code keeps its caller's callee-saved registers and its return address. It
calls `whole`, the whole-block function of the same direction and
implementation, under its symbol `name` (`vg_aes_cfb128_encrypt` and its
variants, `Impl/AesCfb/AArch64.lean`, or decryption's, which the proofs
choose as its registration does), and the block function `b` it is built
on:

1. the registers saved in `save`, and the arguments kept in `x19`
   (schedule), `x20` (rounds), `x21` (iv), `x22` (the data after its whole
   blocks), `x23` (`u = len mod 16`, the bytes after them), `x24` (scratch)
   and `x25` (`save`, restored last);
2. a call of `whole` on the `len / 16` whole blocks, which leaves the last
   ciphertext block `Cₙ₋₁` in `iv`;
3. if `u ≠ 0`, a call of the block function on the block at `iv` in place,
   which leaves `Oₙ = CIPH_K(Cₙ₋₁)` there, as AES-OFB's (`ivArgs`), and the
   first `u` bytes of `Oₙ` XORed into the `u` bytes left, a byte at a time
   (the modes' `xorByte`), the same in both directions;
4. the registers restored.

Only the pointers, `rounds` and `len` can affect timing.
-/

@[expose] public section

namespace VG.Impl.AesCfb.AArch64

open VG.AArch64
open VG.Impl.Aes.AArch64 (Blocks)
open VG.Impl.AesCbc.AArch64 (mov)
open VG.Impl.AesOfb.AArch64 (ivArgs)
open VG.Impl.Modes.AArch64 (xorByte)

/-- The slots of the registers this code saves, in `save` (`x25`, the base of
the restore, last). -/
def finalSaved : List (Reg × Nat) :=
  [(.x19, 0), (.x20, 8), (.x21, 16), (.x22, 24), (.x23, 32), (.x24, 40), (.x30, 48), (.x25, 56)]

/-- The registers saved in `save`, at `x6`. -/
def finalSave : List Instr := finalSaved.map fun (r, d) => .str .x r .x6 d

/-- The arguments to their registers, `x22` and `x23` the data after the
whole blocks and its length, and `x4` the number of whole blocks. -/
def finalMoves : List Instr :=
  [mov .x19 .x0, mov .x20 .x1, mov .x21 .x2, mov .x24 .x5, mov .x25 .x6, .lsr .x .x9 .x4 4,
   .lsl .x .x10 .x9 4, .add .x .x22 .x3 .x10, .sub .x .x23 .x4 .x10, mov .x4 .x9]

/-- The registers saved; the arguments to their registers. -/
def finalSetup : List Instr := finalSave ++ finalMoves

/-- The registers restored, from `save` in `x25`. -/
def finalRestore : List Instr := finalSaved.map fun (r, d) => .ldr .x r .x25 d

/-- The partial last segment: `Oₙ` in place at `iv`, and its first `u`
bytes XORed into the data. -/
def finalTail (b : Blocks) : Prog isa :=
  .seq (.block ivArgs) (.seq (.call b.name b.code)
    (.seq (.block [mov .x9 .x21]) (.loop (.block (xorByte .x22 .x23)) (.nonzero .x .x23))))

/-- The whole function, around a call of the whole-block function `name`,
`whole`, and of the block function `b`. -/
def final (name : String) (whole : Prog isa) (b : Blocks) : Prog isa :=
  .seq (.block finalSetup) (.seq (.call name whole)
    (.seq (.ite (.zero .x .x23) (.block []) (finalTail b)) (.block finalRestore)))

/-- `vg_aes_cfb128_encrypt_final`, calling `vg_aes_cfb128_encrypt` with the
block function `b`, whose callers' names end in `sfx`. -/
def encryptFinal (b : Blocks) (sfx : String) : Prog isa :=
  final ("vg_aes_cfb128_encrypt" ++ sfx) (encrypt b) b

end VG.Impl.AesCfb.AArch64
