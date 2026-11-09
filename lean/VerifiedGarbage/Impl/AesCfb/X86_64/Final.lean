module

public import VerifiedGarbage.Impl.AesCfb.X86_64
public import VerifiedGarbage.Impl.Modes.X86_64.FbFinal

/-!
# AES-CFB128 of a message's last piece: x86-64 implementation

`encryptFinal b sfx` and `decryptFinal b sfx` (schedule = rdi, rounds = rsi,
iv = rdx, data = rcx, len = r8, scratch = r9, save = `[rsp + 8]`): the code
of `vg_aes_cfb128_encrypt_final` and `vg_aes_cfb128_decrypt_final`, whose
registrations frame it with a buffer of their own on the stack, `save`, the
seventh argument, where the code keeps its caller's callee-saved registers.
They are generic over the implementation of the block functions they call
(`b`, whose callers' names end in `sfx`, e.g. `_aesni`):

1. the registers saved in `save`, and the arguments kept in `rbx`
   (schedule), `rbp` (rounds), `r12` (iv), `r13` (the data after its whole
   blocks), `r14` (`u = len mod 16`, the bytes after them) and `r15`
   (scratch);
2. a call of the whole-block function of the same direction and
   implementation (`vg_aes_cfb128_encrypt` and its variants,
   `Impl/AesCfb/X86_64.lean`) on the `len / 16` whole blocks, which leaves
   the last ciphertext block `Cₙ₋₁` in `iv`;
3. if `u ≠ 0`, a call of the block function on the block at `iv` in place,
   which leaves `Oₙ = CIPH_K(Cₙ₋₁)` there, as AES-OFB's (`ivArgs`), and the
   first `u` bytes of `Oₙ` XORed into the `u` bytes left, a byte at a time
   (the modes' `xorByte`), the same in both directions;
4. the registers restored.

Only the pointers, `rounds` and `len` can affect timing.
-/

@[expose] public section

namespace VG.Impl.AesCfb.X86_64

open VG.X86_64
open VG.Impl.Aes.X86_64 (Blocks)
open VG.Impl.AesCbc.X86_64 (at_)
open VG.Impl.AesOfb.X86_64 (ivArgs)
open VG.Impl.Modes.X86_64 (xorByte)

/-- The slots of the registers this code saves, in `save`. -/
def finalSaved : List (Reg × Nat) :=
  [(.rbx, 0), (.rbp, 8), (.r12, 16), (.r13, 24), (.r14, 32), (.r15, 40)]

/-- `save`, from the stack, to `rax`. -/
def loadSave : List Instr := [.mov .rax (.mem (at_ .rsp 8))]

/-- The registers saved in `save`, at `rax`. -/
def finalSave : List Instr := finalSaved.map fun p => .store { base := .rax, disp := p.2 } p.1

/-- The arguments to their registers, `r13` and `r14` the data after the
whole blocks and its length, and `r8` the number of whole blocks. -/
def finalMoves : List Instr :=
  [.mov .rbx (.reg .rdi), .mov .rbp (.reg .rsi), .mov .r12 (.reg .rdx), .mov .r15 (.reg .r9),
   .mov .r14 (.reg .r8), .alu .and .r14 (.imm 15), .mov .r13 (.reg .r8), .alu .sub .r13 (.reg .r14),
   .alu .add .r13 (.reg .rcx), .shift .shr .r8 4]

/-- The registers saved; the arguments to their registers. -/
def finalSetup : List Instr := finalSave ++ finalMoves

/-- The registers restored, from `save` in `rax`. -/
def finalRestore : List Instr := finalSaved.map fun p => .mov p.1 (.mem { base := .rax, disp := p.2 })

/-- The partial last segment: `Oₙ` in place at `iv`, and its first `u`
bytes XORed into the data. -/
def finalTail (b : Blocks) : Prog isa :=
  .seq (.block ivArgs) (.seq (.call b.name b.code)
    (.seq (.block [.mov .rax (.reg .r12)]) (.loop (.block (xorByte .r13 .r14)) .ne)))

/-- The whole function, around a call of the whole-block function `name`,
`whole`. -/
def final (name : String) (whole : Prog isa) (b : Blocks) : Prog isa :=
  .seq (.block loadSave) (.seq (.block finalSetup) (.seq (.call name whole)
    (.seq (.block [.alu .test .r14 (.reg .r14)]) (.seq (.ite .e (.block []) (finalTail b))
      (.seq (.block loadSave) (.block finalRestore))))))

/-- `vg_aes_cfb128_encrypt_final`, calling `vg_aes_cfb128_encrypt` with the
block function `b`, whose callers' names end in `sfx`. -/
def encryptFinal (b : Blocks) (sfx : String) : Prog isa :=
  final ("vg_aes_cfb128_encrypt" ++ sfx) (encrypt b) b

/-- `vg_aes_cfb128_decrypt_final`, calling `vg_aes_cfb128_decrypt`. -/
def decryptFinal (b : Blocks) (sfx : String) : Prog isa :=
  final ("vg_aes_cfb128_decrypt" ++ sfx) (decrypt b) b

end VG.Impl.AesCfb.X86_64
