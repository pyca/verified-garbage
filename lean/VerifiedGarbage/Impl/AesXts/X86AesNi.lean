module

public import VerifiedGarbage.Impl.AesXts.X86
public import VerifiedGarbage.Impl.Aes.X86.AesNiBlocks

/-!
# XTS-AES with AES-NI: x86 (32-bit) implementation

`vg_aes_xts_encrypt_aesni(schedule, rounds, tweak, data, n, scratch)` and
`vg_aes_xts_decrypt_aesni` with the same arguments, every argument on the
stack (cdecl), with the contracts of the whole-block functions of
`Impl/AesXts/X86.lean`, for CPUs with AES-NI: one pass over the data, which
calls nothing.

The registers are saved in the scratch buffer and restored from it as there
(`setup`, `restore`). `eax` holds the schedule, `ecx` the number of rounds,
`edx` the scratch buffer, `esi` the next block, `edi` the number of blocks
left and `ebp` `tweak`; `xmm7` holds the tweak of the next block, between
the groups of blocks.

A group of blocks (`group`): each block is loaded, its tweak, in `xmm7`, is
XORed in and stored at `scratch + 256 + 16 j` (`lane`), and the tweak is
multiplied by `α` for the next block (`fill6`, `fill1`); the rounds are those
of `vg_aes_encrypt_blocks_aesni` and `vg_aes_decrypt_blocks_aesni`
(`Impl.Aes.X86.AesNi.aes`, `aesDec`), each round key through `xmm6`, with a
branch on the public `rounds`; and each block's tweak is XORed in again and
the block stored back (`xorOut`). Six blocks at a time while six are left
(`xmm0`–`xmm5`), then one at a time (`xmm0`). The tweak after the last block
is then stored at `tweak`.

A tweak waits for only two instructions on the one before: it is doubled in
two quadwords (`paddq`), and XORed with the two carries, the one out of the
low quadword and the one out of the high quadword, which is `0x87`. The
carries of the next tweaks are the top bits of the first one's quadwords, one
after the other (what `0x87` changes is far below them), which `signs` puts in
the top bits of two words of `xmm5`; `step` makes the carry of one from a copy
of it (`psraw` and `pand` with the constant in `xmm4`, which `pro` stores once
at `scratch + 368`: the rounds change every other SSE register), and shifts it
for the next (`paddw`). The last two blocks of six take the registers `xmm4`
and `xmm5`, so the carries of the last two tweaks are made before
(`carries2`): the one of block 5 stays in `xmm5`, and the one of the block
after it is kept in the scratch buffer until the blocks are stored (`next6`),
so that the round keys' loads into `xmm6` do not wait for its load where the
processor keeps the registers' upper halves.

Decryption runs the equivalent inverse cipher, as
`vg_aes_decrypt_blocks_aesni` does: `InvMixColumns` of the round keys
(`Impl.Aes.X86.AesNi.imcKeys`) at `scratch + 16 j` and the last round key at
`scratch + 224`, computed once before the blocks.

Only the pointers, `rounds` and `n` can affect timing: the branches are on
`rounds` and `n`.
-/

@[expose] public section

namespace VG.Impl.AesXts.X86AesNi

open VG.X86
open VG.Impl.Aes.X86.AesNi (aes aesDec imcKeys regs6)
open VG.Impl.CmacAes.X86 (argOp at_ setup restore)

/-- The offsets in the scratch buffer of a group's tweaks, of the carry of the
last (`last2`) and of the constant of the carries. -/
def twO : Nat := 256
def rO : Nat := 352
def cO : Nat := 368

/-- The constant of the carries in `xmm4`, and the top bits of the quadwords
of the tweak in `xmm7` and those below them in words of `xmm5`. -/
def signs : List Instr :=
  [.movdquLoad .xmm4 (at_ .edx cO), .xop (.pshufd .xmm5 .xmm7 0x5f), .xop (.shift .psrld .xmm5 16)]

/-- Block `j` of a group loaded into `b` with its tweak, in `xmm7`, XORed in,
and the tweak stored. -/
def lane (b : XReg) (j : Nat) : List Instr :=
  [.movdquLoad b (at_ .esi (16 * j)), .xop (.bin .pxor b .xmm7), .movdquStore (at_ .edx (twO + 16 * j)) .xmm7]

/-- The tweak in `xmm7` times `α`, through `xmm6`. -/
def step : List Instr :=
  [.xop (.bin .movdqa .xmm6 .xmm5), .xop (.shift .psraw .xmm6 15), .xop (.bin .paddw .xmm5 .xmm5),
   .xop (.bin .pand .xmm6 .xmm4), .xop (.bin .paddq .xmm7 .xmm7), .xop (.bin .pxor .xmm7 .xmm6)]

/-- The blocks from block `j` on in the registers, each with its tweak XORed
in, and the tweak of the block after them in `xmm7`. -/
def lanes : List XReg → Nat → List Instr
  | [], _ => []
  | b :: bs, j => lane b j ++ (step ++ lanes bs (j + 1))

/-- The registers of the first four blocks of six. -/
def regs4 : List XReg := [.xmm0, .xmm1, .xmm2, .xmm3]

/-- The carries of the last two tweaks: the one of block 5 in `xmm5`, and the
one of the block after it in the scratch buffer. -/
def carries2 : List Instr :=
  [.xop (.bin .movdqa .xmm6 .xmm5), .xop (.bin .paddw .xmm6 .xmm6), .xop (.shift .psraw .xmm6 15),
   .xop (.bin .pand .xmm6 .xmm4), .movdquStore (at_ .edx rO) .xmm6, .xop (.shift .psraw .xmm5 15),
   .xop (.bin .pand .xmm5 .xmm4)]

/-- The tweak in `xmm7` times `α`, with its carry in `r`. -/
def dblWith (r : XReg) : List Instr := [.xop (.bin .paddq .xmm7 .xmm7), .xop (.bin .pxor .xmm7 r)]

/-- The last two blocks of six. -/
def last2 : List Instr := carries2 ++ (lane .xmm4 4 ++ (dblWith .xmm5 ++ lane .xmm5 5))

/-- Six blocks, with their tweaks XORed in, in `xmm0`–`xmm5`, and the tweak of
the last in `xmm7`. -/
def fill6 : List Instr := signs ++ (lanes regs4 0 ++ last2)

/-- The tweak in `xmm7` times `α`, after six blocks. -/
def next6 : List Instr := .movdquLoad .xmm6 (at_ .edx rO) :: dblWith .xmm6

/-- One block, with its tweak XORed in, in `xmm0`, and the tweak after it in
`xmm7`. -/
def fill1 : List Instr := signs ++ lanes [.xmm0] 0

/-- Each block register with its tweak XORed in, through `xmm6`, stored to
the blocks at `esi + 16 j` on. -/
def xorOut : List XReg → Nat → List Instr
  | [], _ => []
  | b :: bs, j =>
    ([.movdquLoad .xmm6 (at_ .edx (twO + 16 * j)), .xop (.bin .pxor b .xmm6),
      .movdquStore (at_ .esi (16 * j)) b] : List Instr) ++ xorOut bs (j + 1)

/-- The rounds of a direction on the block registers `rs`. -/
def rounds (enc : Bool) (rs : List XReg) : Prog isa := if enc then aes rs else aesDec rs

/-- The blocks at `esi`, which `fill` loads into the registers `rs`, through
XTS, stored back; then `next`, and `rest`. -/
def group (enc : Bool) (fill : List Instr) (rs : List XReg) (next rest : List Instr) : Prog isa :=
  .seq (.block fill) (.seq (rounds enc rs) (.block (xorOut rs 0 ++ (next ++ rest))))

/-- Six blocks, and CF set if fewer than six are left. -/
def six (enc : Bool) : Prog isa :=
  group enc fill6 regs6 next6 [.alu .add .esi (.imm 96), .alu .sub .edi (.imm 6), .alu .cmp .edi (.imm 6)]

/-- One block, and ZF set if none are left. -/
def one (enc : Bool) : Prog isa :=
  group enc fill1 [.xmm0] [] [.alu .add .esi (.imm 16), .alu .sub .edi (.imm 1)]

/-- The constant of the carries, `0x87` in the low quadword and 1 in the high
one, in `xmm6`. -/
def const : List Instr :=
  [.mov .eax (.imm 0x87), .xop (.movd .xmm6 .eax), .mov .eax (.imm 1), .xop (.movd .xmm7 .eax),
   .xop (.bin .punpcklqdq .xmm6 .xmm7)]

/-- The scratch buffer in `edx`, the constant stored in it, and the schedule
and `rounds` in `eax` and `ecx`. -/
def pro : List Instr :=
  ([.mov .edx (argOp 5)] : List Instr) ++ const ++
    ([.movdquStore (at_ .edx cO) .xmm6, .mov .eax (argOp 0), .mov .ecx (argOp 1)] : List Instr)

/-- What decryption computes of the round keys before the blocks. -/
def keys (enc : Bool) : Prog isa := if enc then .block [] else imcKeys

/-- `tweak` in `ebp`, the number of blocks in `edi`, the tweak in `xmm7`,
and CF set if there are fewer than six blocks. -/
def start : List Instr :=
  [.mov .ebp (argOp 2), .mov .edi (argOp 4), .movdquLoad .xmm7 (at_ .ebp 0), .alu .cmp .edi (.imm 6)]

/-- The tweak after the last block stored at `tweak`. -/
def storeT : List Instr := [.movdquStore (at_ .ebp 0) .xmm7]

/-- The blocks, six and then one at a time, after `cmp edi, 6`. -/
def tail (enc : Bool) : Prog isa :=
  .seq (.ite .b (.block []) (.loop (six enc) .ae))
    (.seq (.block [.alu .test .edi (.reg .edi)]) (.ite .e (.block []) (.loop (one enc) .ne)))

/-- The blocks (at least one). -/
def batch (enc : Bool) : Prog isa :=
  .seq (.block pro) (.seq (keys enc) (.seq (.block start) (.seq (tail enc) (.block storeT))))

def crypt (enc : Bool) : Prog isa :=
  .seq (.block setup) (.seq (.ite .e (.block []) (batch enc)) (.block (restore 5)))

/-- `vg_aes_xts_encrypt_aesni`. -/
def encrypt : Prog isa := crypt true

/-- `vg_aes_xts_decrypt_aesni`. -/
def decrypt : Prog isa := crypt false

end VG.Impl.AesXts.X86AesNi
