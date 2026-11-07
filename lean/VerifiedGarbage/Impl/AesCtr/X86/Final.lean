module

public import VerifiedGarbage.Impl.AesCtr.X86
public import VerifiedGarbage.Impl.AesCfb.X86.Final

/-!
# AES-CTR of a message's last piece: x86 (32-bit) implementation

`cryptFinal b sfx` (cdecl: schedule, rounds, ctr, data, len, scratch, save,
every argument on the stack): the code of `vg_aes_ctr_final`, whose
registration frames it with a buffer of its own on the stack, `save`, the
seventh argument, of 32 bytes: the caller's callee-saved registers, then a
block of the code's own. It is generic over the implementation of the block
functions that the whole-block function calls (`b`, whose callers' names end
in `sfx`, e.g. `_aesni`):

1. our caller's `ebx`, `esi`, `edi` and `ebp` saved in `save`, as AES-CFB's
   final functions do (`Impl/AesCfb/X86/Final.lean`);
2. a call of the whole-block function of the same implementation
   (`vg_aes_ctr` and its variants, `Impl/AesCtr/X86.lean`) on the
   `len / 16` whole blocks, its six arguments pushed in a frame of their
   own, which leaves `Tₙ₊₁` in `ctr`;
3. if `u = len mod 16 ≠ 0`, the block after the registers in `save` zeroed,
   a call of the same function on that one block, which leaves
   `CIPH_K(Tₙ₊₁)` there and `Tₙ₊₂` in `ctr`, and the first `u` bytes of the
   block XORed into the `u` bytes left, a byte at a time (the modes'
   `tailByte`: from `ebx`, into `esi`, `ebp` of them);
4. the registers restored.

The registration's frame zeroes `save`, the block included, on return.
Every argument is reloaded from the stack where it is needed. Only the
pointers, `rounds` and `len` can affect timing.
-/

@[expose] public section

namespace VG.Impl.AesCtr.X86

open VG.X86
open VG.Impl.Aes.X86 (Blocks)
open VG.Impl.CmacAes.X86 (argOp at_)
open VG.Impl.AesCfb.X86 (finalSave wholeArgs wholeCall tailTest finalRestore)
open VG.Impl.Modes.X86 (tailByte)

/-- The four words of the block after the registers in `save`, each zeroed
from `ecx`. -/
def zeroSlots : List (Reg × Nat) := [(.ecx, 16), (.ecx, 20), (.ecx, 24), (.ecx, 28)]

/-- `save` (our stack argument 6) to `eax`, and the block after the
registers zeroed. -/
def zeroBlock : List Instr := [.mov .eax (argOp 6), .mov .ecx (.imm 0)] ++ zeroSlots.map fun p => .store (at_ .eax p.2) p.1

/-- The whole-block function's arguments on that block: the schedule, the
rounds, the counter block, the block, `n = 1`, and the working space. -/
def tailMoves : List Instr :=
  [.mov .ebx (.reg .eax), .alu .add .ebx (.imm 16), .mov .eax (argOp 0), .mov .ecx (argOp 1),
   .mov .edx (argOp 2), .mov .esi (.imm 1), .mov .edi (argOp 5)]

/-- The block zeroed, and the arguments of the whole-block function on it. -/
def tailArgs : List Instr := zeroBlock ++ tailMoves

/-- The tail loop's operands: `ebx` the block, `ebp` the `u` bytes left, and
`esi` the data after the whole blocks, `data + (len - u)`. -/
def xorArgs : List Instr :=
  [.mov .ebx (argOp 6), .alu .add .ebx (.imm 16), .mov .esi (argOp 3), .mov .ebp (argOp 4),
   .mov .eax (.reg .ebp), .alu .and .ebp (.imm 15), .alu .sub .eax (.reg .ebp), .alu .add .esi (.reg .eax)]

/-- The partial last block: the output block `CIPH_K(Tₙ₊₁)` in the block of
`save`, by a call of the whole-block function `name`, `whole`, on it, and its
first `u` bytes XORed into the data. -/
def finalTail (name : String) (whole : Prog isa) : Prog isa :=
  .seq (.block tailArgs) (.seq (wholeCall name whole) (.seq (.block xorArgs) (.loop (.block tailByte) .ne)))

/-- The whole function, around calls of the whole-block function `name`,
`whole`. -/
def final (name : String) (whole : Prog isa) : Prog isa :=
  .seq (.block (finalSave ++ wholeArgs)) (.seq (wholeCall name whole)
    (.seq (.block tailTest) (.seq (.ite .e (.block []) (finalTail name whole)) (.block finalRestore))))

/-- `vg_aes_ctr_final`, calling `vg_aes_ctr` with the block function `b`,
whose callers' names end in `sfx`. -/
def cryptFinal (b : Blocks) (sfx : String) : Prog isa := final ("vg_aes_ctr" ++ sfx) (crypt b)

end VG.Impl.AesCtr.X86
