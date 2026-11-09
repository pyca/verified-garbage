module

public import VerifiedGarbage.Impl.AesCfb.RISCV64
public import VerifiedGarbage.Impl.Modes.RISCV64.SeqFinal

/-!
# AES-CFB128 of a message's last piece: RISC-V implementation

`final name whole` (schedule = a0, rounds = a1, iv = a2, data = a3,
len = a4, scratch = a5, save = a6): the code of `vg_aes_cfb128_encrypt_final`
and `vg_aes_cfb128_decrypt_final`, whose registrations frame it with a
buffer of their own on the stack, `save`, the seventh argument, where the
code keeps its return address and its caller's callee-saved registers. It
calls `whole`, the whole-block function of the same direction
(`vg_aes_cfb128_encrypt` or `vg_aes_cfb128_decrypt`,
`Impl/AesCfb/RISCV64.lean`), under its symbol `name`, and the block
function `vg_aes_encrypt_blocks` (`Impl.AesCbc.RISCV64.encCall`, as AES-CTR
and CMAC call it):

1. the return address and the registers saved in `save`, and the arguments
   kept in `s1` (schedule), `s4` (rounds), `s5` (iv), `s6` (scratch), `s2`
   (the data after its whole blocks), `s3` (`u = len mod 16`, the bytes
   after them) and `s7` (`save`, restored last);
2. a call of `whole` on the `len / 16` whole blocks, which leaves the last
   ciphertext block `Cₙ₋₁` in `iv`;
3. if `u ≠ 0`, a call of the block function on the block at `iv` in place,
   which leaves `Oₙ = CIPH_K(Cₙ₋₁)` there, and the first `u` bytes of `Oₙ`
   XORed into the `u` bytes left, a byte at a time (the modes' `xorStep`,
   from `t2`, the block at `iv`, into `s2`, `s3` bytes), the same in both
   directions;
4. the registers restored.

Only the pointers, `rounds` and `len` can affect timing.
-/

@[expose] public section

namespace VG.Impl.AesCfb.RISCV64

open VG.RISCV64
open VG.Impl.AesCbc.RISCV64 (mov encCall)
open VG.Impl.Modes.RISCV64 (xorStep)

/-- The slots of the registers this code saves, in `save` (`s7`, the base of
the restore, last). -/
def finalSaved : List (Reg × Nat) :=
  [(.ra, 0), (.s1, 8), (.s2, 16), (.s3, 24), (.s4, 32), (.s5, 40), (.s6, 48), (.s7, 56)]

/-- The registers saved in `save`, at `a6`. -/
def finalSave : List Instr := finalSaved.map fun (r, d) => .store .d r .a6 d

/-- The arguments to their registers, `s2` and `s3` the data after the
whole blocks and its length, and `a4` the number of whole blocks. -/
def finalMoves : List Instr :=
  [mov .s1 .a0, mov .s4 .a1, mov .s5 .a2, mov .s6 .a5, mov .s7 .a6, .shift .srl .d .t0 .a4 4,
   .shift .sll .d .t1 .t0 4, .add .s2 .a3 .t1, .sub .s3 .a4 .t1, mov .a4 .t0]

/-- The registers saved; the arguments to their registers. -/
def finalSetup : List Instr := finalSave ++ finalMoves

/-- The registers restored, from `save` in `s7`. -/
def finalRestore : List Instr := finalSaved.map fun (r, d) => .load .d r .s7 d

/-- The arguments of the block function on the block at `iv`, in place, one
block, with the scratch buffer as its working space. -/
def ivArgs : List Instr := [mov .a0 .s1, mov .a1 .s4, mov .a2 .s5, .li .a3 1, mov .a4 .s6]

/-- The partial last segment: `Oₙ` in place at `iv`, and its first `u`
bytes XORed into the data. -/
def finalTail : Prog isa :=
  .seq (.block ivArgs) (.seq encCall (.seq (.block [mov .t2 .s5]) (.loop (.block xorStep) (.nonzero .s3))))

/-- The whole function, around a call of the whole-block function `name`,
`whole`. -/
def final (name : String) (whole : Prog isa) : Prog isa :=
  .seq (.block finalSetup) (.seq (.call name whole)
    (.seq (.ite (.zero .s3) (.block []) finalTail) (.block finalRestore)))

/-- `vg_aes_cfb128_encrypt_final`, calling `vg_aes_cfb128_encrypt`. -/
def encryptFinal : Prog isa := final "vg_aes_cfb128_encrypt" encrypt

/-- `vg_aes_cfb128_decrypt_final`, calling `vg_aes_cfb128_decrypt`. -/
def decryptFinal : Prog isa := final "vg_aes_cfb128_decrypt" decrypt

end VG.Impl.AesCfb.RISCV64
