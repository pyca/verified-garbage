module

public import VerifiedGarbage.Impl.CmacAes.X86
public import VerifiedGarbage.Impl.AesOcb.X86

/-!
# XTS-AES: x86 (32-bit) implementation

`vg_aes_xts_encrypt(schedule, rounds, tweak, data, n, scratch)` and
`vg_aes_xts_decrypt` with the same arguments, every argument
on the stack (cdecl), composed of one call of the verified `vg_aes_encrypt_blocks` or
`vg_aes_decrypt_blocks` on all the blocks, in place. They are generic over
the implementation they call (`Blocks`): each is emitted once for each
implementation (e.g. `vg_aes_xts_encrypt_aesni` calls
`vg_aes_encrypt_blocks_aesni`).

They are built from AES-CBC's pieces (`Impl/AesCbc/X86.lean`), whose
arguments are in the same places: the registers are saved in the scratch
buffer and `esi` points at the next block. A pass over the blocks (`pass`)
keeps the tweak in `xmm0`, loaded from `tweak`, takes each block through
`xmm1` (`movdqu`, `pxor`, `movdqu`: `xorBlk`), and multiplies the tweak by
`α` after each (`mulX`), with `edi` the number of blocks left; the block
function enciphers (or deciphers) all the blocks in place (called as AES-OCB
calls it, `Impl/AesOcb/X86.lean`); and a second pass, from the tweak at
`tweak` again, which the first left as it was, XORs the tweaks in again,
after which the tweak after the last block is stored (`storeT`).

`mulX` multiplies the tweak by `α` as its four doublewords, little-endian,
with SSE2 alone: each shifted left by one bit (`paddd` of the register to
itself), and XORed with the top bit of the one before it, or for the first
with `0x87` if the top bit of the last is set. The top bits come from a copy
of the tweak with its doublewords rotated up by one (`pshufd`) and shifted
right by 31 bits (`psrld`): adding all ones to each (`paddd` with `xmm6`)
gives zero where the bit was set and all ones where it was not, and `pandn`
with the doublewords `0x87, 1, 1, 1` (`xmm7`) keeps those where it was set.
`consts` sets up the two constants for each pass, as the block function may
change every SSE register.

Only the pointers, `rounds` and `n` can affect timing: the only branches are
on `n`.
-/

@[expose] public section

namespace VG.Impl.AesXts.X86

open VG.X86
open VG.Impl.Aes.X86 (Blocks)
open VG.Impl.CmacAes.X86 (argOp at_ setup restore)

/-- The tweak at `ebx` times `α`, in memory, a word at a time, with `add` and
`adc` (carrying each word's top bit into the next) and `0x87` XORed into the
first word if the last word's top bit was set, as a mask from `sbb` of the
carry: for a caller that has a tweak in memory to step once
(`Impl/AesXts/X86Unit.lean`). -/
def mulA : List Instr :=
  [.mov .eax (.mem (at_ .ebx 0)), .mov .ecx (.mem (at_ .ebx 4)), .mov .edx (.mem (at_ .ebx 8)),
   .mov .edi (.mem (at_ .ebx 12)), .alu .add .eax (.reg .eax), .alu .adc .ecx (.reg .ecx),
   .alu .adc .edx (.reg .edx), .alu .adc .edi (.reg .edi), .alu .sbb .ebp (.reg .ebp),
   .alu .and .ebp (.imm 0x87), .alu .xor .eax (.reg .ebp), .store (at_ .ebx 0) .eax,
   .store (at_ .ebx 4) .ecx, .store (at_ .ebx 8) .edx, .store (at_ .ebx 12) .edi]

/-- All ones in `xmm6`, and the doublewords `0x87, 1, 1, 1` in `xmm7`, with
`eax` and `xmm5`. -/
def consts : List Instr :=
  [.mov .eax (.imm 0xFFFFFFFF), .xop (.movd .xmm6 .eax), .xop (.pshufd .xmm6 .xmm6 0),
   .mov .eax (.imm 0x86), .xop (.movd .xmm7 .eax), .xop (.bin .movdqa .xmm5 .xmm6),
   .xop (.shift .psrld .xmm5 31), .xop (.bin .pxor .xmm7 .xmm5)]

/-- The tweak in `t` times `α`, with `xmm2` and the constants in `xmm6` and
`xmm7`. -/
def mulX (t : XReg) : List Instr :=
  [.xop (.pshufd .xmm2 t 0x93), .xop (.shift .psrld .xmm2 31), .xop (.bin .paddd .xmm2 .xmm6),
   .xop (.bin .pandn .xmm2 .xmm7), .xop (.bin .paddd t t), .xop (.bin .pxor t .xmm2)]

/-- The tweak in `t` XORed into the block at `esi + 16 j`, through `xmm1`. -/
def xorBlk (t : XReg) (j : Nat) : List Instr :=
  [.movdquLoad .xmm1 (at_ .esi (16 * j)), .xop (.bin .pxor .xmm1 t), .movdquStore (at_ .esi (16 * j)) .xmm1]

/-- One block: the tweak XORed in, the tweak times `α`, and on to the next
block (ZF set after the last). -/
def singleBody : List Instr :=
  xorBlk .xmm0 0 ++ mulX .xmm0 ++ ([.alu .add .esi (.imm 16), .alu .sub .edi (.imm 1)] : List Instr)

/-- The first block in `esi`, `tweak` in `ebx`, the number of blocks in
`edi`, the constants, and the tweak in `xmm0`. -/
def passPro : List Instr :=
  ([.mov .esi (argOp 3), .mov .ebx (argOp 2), .mov .edi (argOp 4)] : List Instr) ++ consts ++
    ([.movdquLoad .xmm0 (at_ .ebx 0)] : List Instr)

/-- Each block (at least one) with its tweak XORed in, from the tweak at
`tweak`, which is left as it is: the tweak after the last block is in
`xmm0`, and `tweak` in `ebx`. -/
def pass : Prog isa := .seq (.block passPro) (.loop (.block singleBody) .ne)

/-- The arguments of the block function on all the blocks: the schedule, the
rounds, the blocks, their number and the working space. -/
def callArgs : List Instr :=
  [.mov .eax (argOp 0), .mov .ecx (argOp 1), .mov .edx (argOp 3), .mov .ebx (argOp 4), .mov .ebp (argOp 5)]

/-- The tweak in `xmm0` stored at `tweak`, which a pass leaves in `ebx`. -/
def storeT : List Instr := [.movdquStore (at_ .ebx 0) .xmm0]

/-- The blocks (at least one): the tweaks XORed in, enciphered (or
deciphered) by `b`, the tweaks XORed in again, and the tweak after the last
block stored. -/
def batch (b : Blocks) : Prog isa :=
  .seq pass (.seq (.block callArgs)
    (.seq (Impl.AesOcb.X86.blocksFrame ⟨b.name, b.code⟩) (.seq pass (.block storeT))))

def crypt (b : Blocks) : Prog isa :=
  .seq (.block setup) (.seq (.ite .e (.block []) (batch b)) (.block (restore 5)))

def encrypt (b : Blocks) : Prog isa := crypt b

def decrypt (b : Blocks) : Prog isa := crypt b

end VG.Impl.AesXts.X86
