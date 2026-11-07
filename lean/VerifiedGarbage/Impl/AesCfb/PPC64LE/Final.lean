module

public import VerifiedGarbage.Impl.AesCfb.PPC64LE
public import VerifiedGarbage.Impl.Modes.PPC64LE.SeqFinal

/-!
# AES-CFB128 of a message's last piece: PPC64LE implementation

`final name whole` (schedule = r3, rounds = r4, iv = r5, data = r6,
len = r7, scratch = r8, save = r9): the code of `vg_aes_cfb128_encrypt_final`
and `vg_aes_cfb128_decrypt_final`, whose registrations frame it with a
buffer of their own on the stack, `save`, the seventh argument, where the
code keeps its return address and its caller's callee-saved registers. It
calls `whole`, the whole-block function of the same direction
(`vg_aes_cfb128_encrypt` or `vg_aes_cfb128_decrypt`,
`Impl/AesCfb/PPC64LE.lean`), under its symbol `name`, and the block
function `vg_aes_encrypt_blocks` (`encCall`):

1. the return address (through `r0`) and the registers saved in `save`, and
   the arguments kept in `r14` (schedule), `r15` (rounds), `r16` (iv), `r19`
   (scratch), as AES-OFB's `ivArgs` reads them, `r31` (the data after its
   whole blocks), `r30` (`u = len mod 16`, the bytes after them) and `r20`
   (`save`, restored last);
2. a call of `whole` on the `len / 16` whole blocks, which leaves the last
   ciphertext block `Cₙ₋₁` in `iv`;
3. if `u ≠ 0`, a call of the block function on the block at `iv` in place,
   which leaves `Oₙ = CIPH_K(Cₙ₋₁)` there, as AES-OFB's (`ivArgs`), and the
   first `u` bytes of `Oₙ` XORed into the `u` bytes left, a byte at a time
   (the modes' `tailByte`, from `r8`, the block at `iv`, into `r31`, `r30`
   bytes), the same in both directions;
4. the registers and the return address restored.

Only the pointers, `rounds` and `len` can affect timing.
-/

@[expose] public section

namespace VG.Impl.AesCfb.PPC64LE

open VG.PPC64LE
open VG.Impl.AesCbc.PPC64LE (mov encCall)
open VG.Impl.AesOfb.PPC64LE (ivArgs)
open VG.Impl.Modes.PPC64LE (tailByte)

/-- The slots of what this code saves, in `save`: the return address (in
`r0`) first, and `r20`, the base of the restore, last. -/
def finalSaved : List (Reg × Nat) :=
  [(.r0, 0), (.r14, 8), (.r15, 16), (.r16, 24), (.r19, 32), (.r30, 40), (.r31, 48), (.r20, 56)]

/-- The return address and the registers saved in `save`, at `r9`. -/
def finalSave : List Instr := .mflr .r0 :: finalSaved.map fun (r, d) => .store .d r .r9 d

/-- The arguments to their registers, `r31` and `r30` the data after the
whole blocks and its length, and `r7` the number of whole blocks. -/
def finalMoves : List Instr :=
  [mov .r14 .r3, mov .r15 .r4, mov .r16 .r5, mov .r19 .r8, mov .r20 .r9, .lsr .d .r10 .r7 4,
   .lsl .r11 .r10 4, .add .r31 .r6 .r11, .sub .r30 .r7 .r11, mov .r7 .r10]

/-- The registers saved; the arguments to their registers. -/
def finalSetup : List Instr := finalSave ++ finalMoves

/-- The registers and the return address restored, from `save` in `r20`. -/
def finalRestore : List Instr := finalSaved.map (fun (r, d) => .load .d r .r20 d) ++ [.mtlr .r0]

/-- The partial last segment: `Oₙ` in place at `iv`, and its first `u`
bytes XORed into the data. -/
def finalTail : Prog isa :=
  .seq (.block ivArgs) (.seq encCall
    (.seq (.block [mov .r8 .r16]) (.loop (.block tailByte) (.nonzero .d .r30))))

/-- The whole function, around a call of the whole-block function `name`,
`whole`. -/
def final (name : String) (whole : Prog isa) : Prog isa :=
  .seq (.block finalSetup) (.seq (.call name whole)
    (.seq (.ite (.zero .d .r30) (.block []) finalTail) (.block finalRestore)))

/-- `vg_aes_cfb128_encrypt_final`, calling `vg_aes_cfb128_encrypt`. -/
def encryptFinal : Prog isa := final "vg_aes_cfb128_encrypt" encrypt

/-- `vg_aes_cfb128_decrypt_final`, calling `vg_aes_cfb128_decrypt`. -/
def decryptFinal : Prog isa := final "vg_aes_cfb128_decrypt" decrypt

end VG.Impl.AesCfb.PPC64LE
