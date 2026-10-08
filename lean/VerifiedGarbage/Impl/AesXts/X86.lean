import VerifiedGarbage.Impl.AesCbc.X86
import VerifiedGarbage.Impl.AesOcb.X86

/-!
# XTS-AES: x86 (32-bit) implementation

`vg_aes_xts_encrypt(schedule, rounds, tweak, data, n, scratch)` and
`vg_aes_xts_decrypt` with the same arguments (see
`VG.Spec.Xts.aesEncryptContract` and `aesDecryptContract`), every argument
on the stack (cdecl), composed of one call of the verified `vg_aes_encrypt_blocks` or
`vg_aes_decrypt_blocks` on all the blocks, in place. They are generic over
the implementation they call (`Blocks`): each is emitted once for each
implementation (e.g. `vg_aes_xts_encrypt_aesni` calls
`vg_aes_encrypt_blocks_aesni`).

They are built from AES-CBC's pieces (`Impl/AesCbc/X86.lean`), whose
arguments are in the same places: `esi` points at the next block, and the
other arguments are reloaded from the stack. The tweak `T` is saved at
`scratch + 2048`; a pass over the blocks XORs each block's tweak into it,
multiplying the tweak by `α` after each (`pass`); `T` is restored, the block
function enciphers (or deciphers) all the blocks in place (called as AES-OCB
calls it, `Impl/AesOcb/X86.lean`), and a second pass XORs the tweaks in
again, leaving the tweak after the last block. The tweak is multiplied by
`α` as its four words, little-endian, shifted left by `add` and `adc`
(carrying each word's top bit into the next), and `0x87` XORed into the
first word if the last word's top bit was set, as a mask from `sbb` of the
carry.

Only the pointers, `rounds` and `n` can affect timing: the only branches are
on `n`.
-/

namespace VG.Impl.AesXts.X86

open VG.X86
open VG.Impl.Aes.X86 (Blocks)
open VG.Impl.CmacAes.X86 (argOp at_ setup advance restore xor4 zero4)
open VG.Impl.AesCbc.X86 (cOff)

/-- The tweak at `ebx` times `α`. -/
def mulA : List Instr :=
  [.mov .eax (.mem (at_ .ebx 0)), .mov .ecx (.mem (at_ .ebx 4)), .mov .edx (.mem (at_ .ebx 8)),
   .mov .edi (.mem (at_ .ebx 12)), .alu .add .eax (.reg .eax), .alu .adc .ecx (.reg .ecx),
   .alu .adc .edx (.reg .edx), .alu .adc .edi (.reg .edi), .alu .sbb .ebp (.reg .ebp),
   .alu .and .ebp (.imm 0x87), .alu .xor .eax (.reg .ebp), .store (at_ .ebx 0) .eax,
   .store (at_ .ebx 4) .ecx, .store (at_ .ebx 8) .edx, .store (at_ .ebx 12) .edi]

/-- One block: the tweak XORed in, the tweak times `α`, and on to the next
block (ZF set after the last). -/
def passBody : List Instr := [.mov .ebx (argOp 2)] ++ xor4 .esi .ebx .esi 0 0 0 ++ mulA ++ advance

/-- Each block from `esi` on (at least one) with its tweak XORed in. -/
def pass : Prog isa := .loop (.block passBody) .ne

/-- `T` saved. -/
def saveT : List Instr :=
  [.mov .ebx (argOp 2), .mov .ebp (argOp 5)] ++ zero4 .ebp cOff ++ xor4 .ebp .ebx .ebp cOff 0 cOff

/-- `T` restored, `esi` back at the first block, and the arguments of the
block function on all the blocks: the schedule, the rounds, the blocks, their
number and the working space. -/
def callArgs : List Instr :=
  [.mov .ebx (argOp 2), .mov .ebp (argOp 5)] ++ zero4 .ebx 0 ++ xor4 .ebx .ebp .ebx 0 cOff 0 ++
  [.mov .esi (argOp 3), .mov .eax (argOp 0), .mov .ecx (argOp 1), .mov .edx (.reg .esi), .mov .ebx (argOp 4)]

/-- The blocks (at least one): the tweaks XORed in, enciphered (or
deciphered) by `b`, and the tweaks XORed in again. -/
def batch (b : Blocks) : Prog isa :=
  .seq (.block saveT) (.seq pass (.seq (.block callArgs)
    (.seq (Impl.AesOcb.X86.blocksFrame ⟨b.name, b.code⟩) pass)))

def crypt (b : Blocks) : Prog isa :=
  .seq (.block setup) (.seq (.ite .e (.block []) (batch b)) (.block (restore 5)))

def encrypt (b : Blocks) : Prog isa := crypt b

def decrypt (b : Blocks) : Prog isa := crypt b

end VG.Impl.AesXts.X86
