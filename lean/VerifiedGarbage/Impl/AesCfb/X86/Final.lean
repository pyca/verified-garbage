module

public import VerifiedGarbage.Impl.AesCfb.X86
public import VerifiedGarbage.Impl.Modes.X86.SeqFinal

/-!
# AES-CFB128 of a message's last piece: x86 (32-bit) implementation

`encryptFinal b sfx` and `decryptFinal b sfx` (cdecl: schedule, rounds, iv,
data, len, scratch, save, every argument on the stack): the code of
`vg_aes_cfb128_encrypt_final` and `vg_aes_cfb128_decrypt_final`, whose
registrations frame it with a buffer of their own on the stack, `save`, the
seventh argument, where the code keeps its caller's callee-saved registers.
They are generic over the implementation of the block functions they call
(`b`, whose callers' names end in `sfx`, e.g. `_aesni`):

1. our caller's `ebx`, `esi`, `edi` and `ebp` saved in `save`;
2. a call of the whole-block function of the same direction and
   implementation (`vg_aes_cfb128_encrypt` and its variants,
   `Impl/AesCfb/X86.lean`) on the `len / 16` whole blocks, its six
   arguments pushed in a frame of their own, which leaves the last
   ciphertext block `Cₙ₋₁` in `iv`;
3. if `u = len mod 16` bytes are left, a call of the block function on the
   block at `iv` in place, which leaves `Oₙ = CIPH_K(Cₙ₋₁)` there, as
   AES-OFB's (`ivArgs`, `blkCall`), and the first `u` bytes of `Oₙ` XORed
   into the `u` bytes after the whole blocks, a byte at a time (the modes'
   `tailByte`: from `ebx`, into `esi`, `ebp` of them), the same in both
   directions;
4. the registers restored.

Every argument is reloaded from the stack where it is needed. Only the
pointers, `rounds` and `len` can affect timing.
-/

@[expose] public section

namespace VG.Impl.AesCfb.X86

open VG.X86
open VG.Impl.Aes.X86 (Blocks)
open VG.Impl.CmacAes.X86 (argOp at_)
open VG.Impl.AesCbc.X86 (blkCall)
open VG.Impl.AesOfb.X86 (ivArgs)
open VG.Impl.Modes.X86 (tailByte)

/-- The slots of the registers this code saves, in `save`. -/
def finalSaved : List (Reg × Nat) := [(.ebx, 0), (.esi, 4), (.edi, 8), (.ebp, 12)]

/-- `save` (our stack argument 6) to `eax`, and the registers saved there. -/
def finalSave : List Instr := .mov .eax (argOp 6) :: finalSaved.map fun p => .store (at_ .eax p.2) p.1

/-- The whole-block function's arguments: ours, but the number of whole
blocks, `len >> 4`, for `len`. -/
def wholeArgs : List Instr :=
  [.mov .eax (argOp 0), .mov .ecx (argOp 1), .mov .edx (argOp 2), .mov .ebx (argOp 3), .mov .esi (argOp 4),
   .shift .shr .esi 4, .mov .edi (argOp 5)]

/-- The call of the whole-block function `name(eax, ecx, edx, ebx, esi, edi)`,
its arguments pushed last to first. -/
def wholeCall (name : String) (whole : Prog isa) : Prog isa :=
  .frame (.push [.edi, .esi, .ebx, .edx, .ecx, .eax]) (.call name whole) (.pop .eax 6)

/-- ZF set if no bytes are left after the whole blocks. -/
def tailTest : List Instr := [.mov .eax (argOp 4), .alu .and .eax (.imm 15), .alu .test .eax (.reg .eax)]

/-- The tail loop's operands: `ebx` the block at `iv`, `ebp` the `u` bytes
left, and `esi` the data after the whole blocks, `data + (len - u)`. -/
def xorArgs : List Instr :=
  [.mov .ebx (argOp 2), .mov .esi (argOp 3), .mov .ebp (argOp 4), .mov .eax (.reg .ebp),
   .alu .and .ebp (.imm 15), .alu .sub .eax (.reg .ebp), .alu .add .esi (.reg .eax)]

/-- The registers restored, from `save`. -/
def finalRestore : List Instr := .mov .eax (argOp 6) :: finalSaved.map fun p => .mov p.1 (.mem (at_ .eax p.2))

/-- The partial last segment: `Oₙ` in place at `iv`, and its first `u`
bytes XORed into the data. -/
def finalTail (b : Blocks) : Prog isa :=
  .seq (.block ivArgs) (.seq (blkCall b) (.seq (.block xorArgs) (.loop (.block tailByte) .ne)))

/-- The whole function, around a call of the whole-block function `name`,
`whole`. -/
def final (name : String) (whole : Prog isa) (b : Blocks) : Prog isa :=
  .seq (.block (finalSave ++ wholeArgs)) (.seq (wholeCall name whole)
    (.seq (.block tailTest) (.seq (.ite .e (.block []) (finalTail b)) (.block finalRestore))))

/-- `vg_aes_cfb128_encrypt_final`, calling `vg_aes_cfb128_encrypt` with the
block function `b`, whose callers' names end in `sfx`. -/
def encryptFinal (b : Blocks) (sfx : String) : Prog isa :=
  final ("vg_aes_cfb128_encrypt" ++ sfx) (encrypt b) b

/-- `vg_aes_cfb128_decrypt_final`, calling `vg_aes_cfb128_decrypt`. -/
def decryptFinal (b : Blocks) (sfx : String) : Prog isa :=
  final ("vg_aes_cfb128_decrypt" ++ sfx) (decrypt b) b

end VG.Impl.AesCfb.X86
