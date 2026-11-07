module

public import VerifiedGarbage.Impl.Sm4.X86.Ctr
public import VerifiedGarbage.Impl.AesCtr.X86.Final
public import VerifiedGarbage.Impl.StackScratch.X86

/-!
# SM4-CTR of a message's last piece: x86 (32-bit) implementation

`ctrFinal` (cdecl: schedule, ctr, data, len, save, every argument on the
stack): the code of `vg_sm4_ctr_final`, whose registration frames it with a
buffer of its own on the stack, `save`, the fifth argument, of 32 bytes: the
caller's callee-saved registers, then a block of the code's own. It is
AES-CTR's final function's (`Impl/AesCtr/X86/Final.lean`) with SM4's
arguments, around calls of `vg_sm4_ctr`, framed by its own working space on
the stack (`ctrFramed`), its four arguments pushed in a frame of their own
(`ctrCall`):

1. our caller's `ebx`, `esi`, `edi` and `ebp` saved in `save`;
2. a call of `vg_sm4_ctr` on the `len / 16` whole blocks, which leaves
   `Tₙ₊₁` in `ctr`;
3. if `u = len mod 16 ≠ 0`, the block after the registers in `save` zeroed,
   a call of `vg_sm4_ctr` on that one block, which leaves `CIPH_K(Tₙ₊₁)`
   there and `Tₙ₊₂` in `ctr`, and the first `u` bytes of the block XORed
   into the `u` bytes left, a byte at a time (the modes' `tailByte`: from
   `ebx`, into `esi`, `ebp` of them);
4. the registers restored.

The registration's frame zeroes `save`, the block included, on return.
Every argument is reloaded from the stack where it is needed. Only the
pointers and `len` can affect timing.
-/

@[expose] public section

namespace VG.Impl.Sm4.X86

open VG.X86
open VG.Impl.CmacAes.X86 (argOp at_)
open VG.Impl.AesCfb.X86 (finalSaved)
open VG.Impl.AesCtr.X86 (zeroSlots)
open VG.Impl.Modes.X86 (tailByte)

/-- `vg_sm4_ctr`, with its working space on the stack. -/
def ctrFramed : Prog isa := Impl.StackScratch.X86.withStackScratchWiped 1496 4 368 ctr

/-- `save` (our stack argument 4) to `eax`, and the registers saved there. -/
def ctrFinalSave : List Instr := .mov .eax (argOp 4) :: finalSaved.map fun p => .store (at_ .eax p.2) p.1

/-- The arguments of `vg_sm4_ctr` on the whole blocks: ours, but the number
of whole blocks, `len >> 4`, for `len`. -/
def ctrFinalArgs : List Instr :=
  [.mov .eax (argOp 0), .mov .edx (argOp 1), .mov .ebx (argOp 2), .mov .esi (argOp 3), .shift .shr .esi 4]

/-- The call of `vg_sm4_ctr(eax, edx, ebx, esi)`, its arguments pushed last
to first. -/
def ctrCall : Prog isa := .frame (.push [.esi, .ebx, .edx, .eax]) (.call "vg_sm4_ctr" ctrFramed) (.pop .eax 4)

/-- ZF set if no bytes are left after the whole blocks. -/
def ctrFinalTest : List Instr := [.mov .eax (argOp 3), .alu .and .eax (.imm 15), .alu .test .eax (.reg .eax)]

/-- The block after the registers in `save` zeroed, and the arguments of
`vg_sm4_ctr` on it: the schedule, the counter block, the block and
`n = 1`. -/
def ctrFinalTailArgs : List Instr :=
  [.mov .eax (argOp 4), .mov .ecx (.imm 0)] ++ zeroSlots.map (fun p => .store (at_ .eax p.2) p.1) ++
    [.mov .ebx (.reg .eax), .alu .add .ebx (.imm 16), .mov .eax (argOp 0), .mov .edx (argOp 1),
     .mov .esi (.imm 1)]

/-- The tail loop's operands: `ebx` the block, `ebp` the `u` bytes left, and
`esi` the data after the whole blocks, `data + (len - u)`. -/
def ctrFinalXorArgs : List Instr :=
  [.mov .ebx (argOp 4), .alu .add .ebx (.imm 16), .mov .esi (argOp 2), .mov .ebp (argOp 3),
   .mov .eax (.reg .ebp), .alu .and .ebp (.imm 15), .alu .sub .eax (.reg .ebp), .alu .add .esi (.reg .eax)]

/-- The registers restored, from `save`. -/
def ctrFinalRestore : List Instr := .mov .eax (argOp 4) :: finalSaved.map fun p => .mov p.1 (.mem (at_ .eax p.2))

/-- The partial last block: the output block `CIPH_K(Tₙ₊₁)` in the block of
`save`, and its first `u` bytes XORed into the data. -/
def ctrFinalTail : Prog isa :=
  .seq (.block ctrFinalTailArgs) (.seq ctrCall (.seq (.block ctrFinalXorArgs) (.loop (.block tailByte) .ne)))

/-- `vg_sm4_ctr_final`. -/
def ctrFinal : Prog isa :=
  .seq (.block (ctrFinalSave ++ ctrFinalArgs)) (.seq ctrCall
    (.seq (.block ctrFinalTest) (.seq (.ite .e (.block []) ctrFinalTail) (.block ctrFinalRestore))))

end VG.Impl.Sm4.X86
