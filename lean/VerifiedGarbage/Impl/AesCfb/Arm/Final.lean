module

public import VerifiedGarbage.Impl.AesCfb.Arm
public import VerifiedGarbage.Impl.Modes.Arm.SeqFinal

/-!
# AES-CFB128 of a message's last piece: 32-bit ARM implementation

`encryptFinal` and `decryptFinal` (schedule = r0, rounds = r1, iv = r2,
data = r3, len = `[sp]`, scratch = `[sp + 4]`, save = `[sp + 8]`): the code of
`vg_aes_cfb128_encrypt_final` and `vg_aes_cfb128_decrypt_final`, whose
registrations frame it with a buffer of their own on the stack, `save`, the
seventh argument, where the code keeps its caller's callee-saved registers
and its return address:

1. the registers saved in `save` (through `r12`), and the arguments kept in
   `r4` (schedule), `r5` (rounds), `r6` (iv), `r7` (the data after its whole
   blocks), `r8` (`u = len mod 16`, the bytes after them) and `r10`
   (scratch);
2. a call of the whole-block function of the same direction
   (`vg_aes_cfb128_encrypt` or `vg_aes_cfb128_decrypt`,
   `Impl/AesCfb/Arm.lean`) on the `len / 16` whole blocks, in a frame that
   pushes its stack arguments (`push {r12, lr}`, the number of blocks and the
   scratch buffer), which leaves the last ciphertext block `Cₙ₋₁` in `iv`;
3. if `u ≠ 0`, a call of `vg_aes_encrypt_blocks` on the block at `iv` in
   place, which leaves `Oₙ = CIPH_K(Cₙ₋₁)` there, as AES-OFB's (`ivArgs`,
   `encFrame`), and the first `u` bytes of `Oₙ` XORed into the `u` bytes
   left, a byte at a time (the modes' `xorByte`, through `r0`, `r6`, `r7`,
   `r9` and `r10`), the same in both directions;
4. the registers restored from `save`, whose address is reloaded from the
   stack.

The calls use 16 bytes of stack: the whole-block function's frame and the
one it pushes around each call of the block function. Only the pointers,
`rounds` and `len` can affect timing.
-/

@[expose] public section

namespace VG.Impl.AesCfb.Arm

open VG.Arm
open VG.Impl.CmacAes.Arm (mov)
open VG.Impl.AesCbc.Arm (encFrame)
open VG.Impl.AesOfb.Arm (ivArgs)
open VG.Impl.Modes.Arm (xorByte)

/-- The slots of the registers this code saves, in `save`: every
callee-saved register and `lr`. -/
def finalSaved : List (Reg × Nat) :=
  [(.r4, 0), (.r5, 4), (.r6, 8), (.r7, 12), (.r8, 16), (.r9, 20), (.r10, 24), (.r11, 28), (.lr, 32)]

/-- `save`, the third stack argument, to `r12`. -/
def loadSave : List Instr := [.ldrSp .r12 8]

/-- The registers saved in `save`, at `r12`. -/
def finalSave : List Instr := finalSaved.map fun p => .str p.1 .r12 p.2

/-- The arguments to their registers: `r7` the data after the whole blocks,
`r8` the bytes after them, and `r12` and `lr` the number of whole blocks and
the scratch buffer, the whole-block function's stack arguments. -/
def finalMoves : List Instr :=
  [mov .r4 .r0, mov .r5 .r1, mov .r6 .r2, .ldrSp .r8 0, .ldrSp .r10 4, .mov .r12 (.shifted .r8 .lsr 4),
   .dp .and .r8 .r8 (.imm 15), .dp .add .r7 .r3 (.shifted .r12 .lsl 4), mov .lr .r10]

/-- The registers saved; the arguments to their registers. -/
def finalSetup : List Instr := loadSave ++ finalSave ++ finalMoves

/-- The whole-block function `whole`, called `name`, with its stack
arguments in `r12` and `lr` pushed. -/
def wholeFrame (name : String) (whole : Prog isa) : Prog isa :=
  .frame (.push [.r12, .lr]) (.call name whole) (.pop .r12 8)

/-- The partial last segment: `Oₙ` in place at `iv`, and its first `u` bytes
XORed into the data. -/
def finalTail : Prog isa :=
  .seq (.block ivArgs) (.seq encFrame
    (.seq (.block [mov .r0 .r6, mov .r6 .r7, mov .r7 .r8]) (.loop (.block xorByte) .ne)))

/-- The registers restored, from `save` in `r12`. -/
def finalRestore : List Instr := finalSaved.map fun p => .ldr p.1 .r12 p.2

/-- `save` reloaded, and the registers restored. -/
def finalEnd : List Instr := loadSave ++ finalRestore

/-- The whole function, around a call of the whole-block function `whole`,
called `name`. -/
def final (name : String) (whole : Prog isa) : Prog isa :=
  .seq (.block finalSetup) (.seq (wholeFrame name whole)
    (.seq (.block [.cmp .r8 (.imm 0)]) (.seq (.ite .eq (.block []) finalTail) (.block finalEnd))))

/-- `vg_aes_cfb128_encrypt_final`, calling `vg_aes_cfb128_encrypt`. -/
def encryptFinal : Prog isa := final "vg_aes_cfb128_encrypt" encrypt

/-- `vg_aes_cfb128_decrypt_final`, calling `vg_aes_cfb128_decrypt`. -/
def decryptFinal : Prog isa := final "vg_aes_cfb128_decrypt" decrypt

end VG.Impl.AesCfb.Arm
