module

public import VerifiedGarbage.Impl.CmacAes.X86
public import VerifiedGarbage.Impl.AesOcb.X86
public import VerifiedGarbage.Impl.StackScratch.X86

/-!
# CBC and CFB128 decryption around a block function, on x86 (32-bit)

`groups b cbc (schedule, rounds, iv, data, n, scratch, buf)`, every argument
on the stack (cdecl): decryption of `n` blocks in place, in CBC (`cbc`,
around `vg_aes_decrypt_blocks`) or CFB128 (around `vg_aes_encrypt_blocks`),
for a block function `b`, as many as 64 blocks a call. Neither mode's blocks
depend on each other in decryption, and a block function of many blocks
bitslices its round keys once for all of them, and takes blocks several at a
time.

Each group of `m` blocks, 64 of them or those left, whichever is fewer:

1. the chaining values `C₀ … Cₘ₋₁`, the block at `iv` and the group's
   ciphertext blocks but the last, are copied to `buf` (`fillBody`), and the
   last, `Cₘ`, to `iv`;
2. one call of `b` on `m` blocks in place: in CBC, the data, which becomes
   `CIPH⁻¹_K(Cⱼ)`; in CFB128, `buf`, which becomes `CIPH_K(Cⱼ₋₁)`;
3. `buf` is XORed into the data (`xorBody`).

`esi` points at the group's first block, `edi` holds the number of blocks
left and `ebx` that of the group, all kept by the callee; the other
arguments are reloaded from the stack where they are needed. Our caller's
`ebx`, `esi`, `edi` and `ebp` are saved at `buf + 1024`.

`buf` (1040 bytes) is a frame of the caller's (`framed`:
`Impl.StackScratch.X86.withStackScratch`), which its cleanup zeroes with the
rest of the stack; of `scratch`, only what `b` writes of the first 2048 bytes
changes.

Only the pointers, `rounds` and `n` can affect timing: the only branches are
on `n`.
-/

@[expose] public section

namespace VG.Impl.AesCbc.X86.Groups

open VG.X86
open VG.Impl.Aes.X86 (Blocks)
open VG.Impl.CmacAes.X86 (argOp at_)

/-- The callee-saved registers, and where they are saved in `buf`. -/
def saved : List (Reg × Nat) := [(.ebx, 1024), (.esi, 1028), (.edi, 1032), (.ebp, 1036)]

/-- The registers saved in `buf` (our stack argument 6), the first block in
`esi` and the number of blocks in `edi`; ZF set if there are none. -/
def setup : List Instr :=
  .mov .eax (argOp 6) :: (saved.map (fun p => .store (at_ .eax p.2) p.1) ++
    ([.mov .esi (argOp 3), .mov .edi (argOp 4), .alu .test .edi (.reg .edi)] : List Instr))

/-- The registers restored. -/
def restore : List Instr := .mov .eax (argOp 6) :: saved.map fun p => .mov p.1 (.mem (at_ .eax p.2))

/-- The group's number of blocks, if it is whole; CF set if it is not. -/
def sizePre : List Instr := [.mov .ebx (.imm 64), .alu .cmp .edi (.imm 64)]

/-- The group's number of blocks in `ebx`. -/
def size : Prog isa := .seq (.block sizePre) (.ite .b (.block [.mov .ebx (.reg .edi)]) (.block []))

/-- `iv` in `ebp` and the block there in `xmm0`, the group in `eax`, `buf` in
`edx` and the number of blocks in `ecx`. -/
def fillPre : List Instr :=
  [.mov .ebp (argOp 2), .movdquLoad .xmm0 (at_ .ebp 0), .mov .eax (.reg .esi), .mov .edx (argOp 6),
   .mov .ecx (.reg .ebx)]

/-- One chaining value to `buf`, and the next, the block's ciphertext, into
`xmm0`. -/
def fillBody : List Instr :=
  [.movdquStore (at_ .edx 0) .xmm0, .movdquLoad .xmm0 (at_ .eax 0), .alu .add .eax (.imm 16),
   .alu .add .edx (.imm 16), .alu .sub .ecx (.imm 1)]

/-- The last ciphertext block to `iv`, and the arguments of the block
function: the schedule, the rounds, the blocks (the group, or `buf`), their
number (in `ebx`) and the working space. -/
def callArgs (cbc : Bool) : List Instr :=
  [.movdquStore (at_ .ebp 0) .xmm0, .mov .eax (argOp 0), .mov .ecx (argOp 1),
   .mov .edx (if cbc then .reg .esi else argOp 6), .mov .ebp (argOp 5)]

/-- Everything before the call. -/
def fill (cbc : Bool) : Prog isa :=
  .seq size (.seq (.block fillPre) (.seq (.loop (.block fillBody) .ne) (.block (callArgs cbc))))

/-- `buf` in `edx`, and the number of blocks in `ecx`. -/
def xorPre : List Instr := [.mov .edx (argOp 6), .mov .ecx (.reg .ebx)]

/-- One block of `buf` XORed into the data. -/
def xorBody : List Instr :=
  [.movdquLoad .xmm0 (at_ .esi 0), .movdquLoad .xmm1 (at_ .edx 0), .xop (.bin .pxor .xmm0 .xmm1),
   .movdquStore (at_ .esi 0) .xmm0, .alu .add .esi (.imm 16), .alu .add .edx (.imm 16),
   .alu .sub .ecx (.imm 1)]

/-- Everything after the call; ZF set if no blocks are left. -/
def finish : Prog isa :=
  .seq (.block xorPre) (.seq (.loop (.block xorBody) .ne) (.block [.alu .sub .edi (.reg .ebx)]))

/-- One group. -/
def body (b : Blocks) (cbc : Bool) : Prog isa :=
  .seq (fill cbc) (.seq (Impl.AesOcb.X86.blocksFrame ⟨b.name, b.code⟩) finish)

/-- The whole function, with `buf` its seventh argument. -/
def groups (b : Blocks) (cbc : Bool) : Prog isa :=
  .seq (.block setup) (.seq (.ite .e (.block []) (.loop (body b cbc) .ne)) (.block restore))

/-- The bytes of the frame that holds `buf`, with a return address's word,
the six arguments and `buf`'s address below it, and 12 more bytes: with
`esp + 4` a multiple of 16 on entry, as the calling convention has it, `buf`
is too. -/
def bufFrame : Nat := 1084

/-- The whole function, with `buf` on the stack. -/
def framed (b : Blocks) (cbc : Bool) : Prog isa :=
  Impl.StackScratch.X86.withStackScratch bufFrame 6 (groups b cbc)

end VG.Impl.AesCbc.X86.Groups
