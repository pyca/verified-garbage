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

A group of blocks in the registers `rs` (`group`): the tweaks of its blocks
are stored at `scratch + 256 + 16 j`, each from `xmm7`, which is then
multiplied by `α` (`mulT`, as `Impl.AesXts.X86.mulX`, with the two constants
loaded from `scratch + 352` and `scratch + 368`, where `pro` stores them
once: the rounds change every other SSE register); each block is loaded and
its tweak XORed in, through `xmm6` (`xorIn`); the rounds are those of
`vg_aes_encrypt_blocks_aesni` and `vg_aes_decrypt_blocks_aesni`
(`Impl.Aes.X86.AesNi.aes`, `aesDec`), each round key through `xmm6`, with a
branch on the public `rounds`; and each block's tweak is XORed in again and
the block stored back (`xorOut`). Six blocks at a time while six are left
(`xmm0`–`xmm5`), then one at a time (`xmm0`). The tweak after the last block
is then stored at `tweak`.

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

/-- The offsets in the scratch buffer of a group's tweaks and of the two
constants of `mulT`. -/
def twO : Nat := 256
def onesO : Nat := 352
def cO : Nat := 368

/-- The tweak in `xmm7` times `α`, with `xmm4`, all ones in `xmm5` and the
doublewords `0x87, 1, 1, 1` in `xmm6`. -/
def mulT : List Instr :=
  [.xop (.pshufd .xmm4 .xmm7 0x93), .xop (.shift .psrld .xmm4 31), .xop (.bin .paddd .xmm4 .xmm5),
   .xop (.bin .pandn .xmm4 .xmm6), .xop (.bin .paddd .xmm7 .xmm7), .xop (.bin .pxor .xmm7 .xmm4)]

/-- The tweak of block `j` of a group stored, and the tweak times `α`. -/
def tweak (j : Nat) : List Instr := .movdquStore (at_ .edx (twO + 16 * j)) .xmm7 :: mulT

/-- The tweaks of `n` blocks of a group, from block `j`. -/
def tweaks : Nat → Nat → List Instr
  | _, 0 => []
  | j, n + 1 => tweak j ++ tweaks (j + 1) n

/-- The two constants loaded, and the tweaks of the `n` blocks of a group. -/
def gen (n : Nat) : List Instr :=
  ([.movdquLoad .xmm5 (at_ .edx onesO), .movdquLoad .xmm6 (at_ .edx cO)] : List Instr) ++ tweaks 0 n

/-- The blocks at `esi + 16 j` on into the block registers, each with its
tweak XORed in, through `xmm6`. -/
def xorIn : List XReg → Nat → List Instr
  | [], _ => []
  | b :: bs, j =>
    ([.movdquLoad b (at_ .esi (16 * j)), .movdquLoad .xmm6 (at_ .edx (twO + 16 * j)),
      .xop (.bin .pxor b .xmm6)] : List Instr) ++ xorIn bs (j + 1)

/-- Each block register with its tweak XORed in, through `xmm6`, stored to
the blocks at `esi + 16 j` on. -/
def xorOut : List XReg → Nat → List Instr
  | [], _ => []
  | b :: bs, j =>
    ([.movdquLoad .xmm6 (at_ .edx (twO + 16 * j)), .xop (.bin .pxor b .xmm6),
      .movdquStore (at_ .esi (16 * j)) b] : List Instr) ++ xorOut bs (j + 1)

/-- The rounds of a direction on the block registers `rs`. -/
def rounds (enc : Bool) (rs : List XReg) : Prog isa := if enc then aes rs else aesDec rs

/-- The blocks at `esi` in the registers `rs` through XTS, stored back; then
`rest`. -/
def group (enc : Bool) (rs : List XReg) (rest : List Instr) : Prog isa :=
  .seq (.block (gen rs.length ++ xorIn rs 0)) (.seq (rounds enc rs) (.block (xorOut rs 0 ++ rest)))

/-- Six blocks, and CF set if fewer than six are left. -/
def six (enc : Bool) : Prog isa :=
  group enc regs6 [.alu .add .esi (.imm 96), .alu .sub .edi (.imm 6), .alu .cmp .edi (.imm 6)]

/-- One block, and ZF set if none are left. -/
def one (enc : Bool) : Prog isa := group enc [.xmm0] [.alu .add .esi (.imm 16), .alu .sub .edi (.imm 1)]

/-- The scratch buffer in `edx`, the two constants stored in it, and the
schedule and `rounds` in `eax` and `ecx`. -/
def pro : List Instr :=
  ([.mov .edx (argOp 5)] : List Instr) ++ Impl.AesXts.X86.consts ++
    ([.movdquStore (at_ .edx onesO) .xmm6, .movdquStore (at_ .edx cO) .xmm7, .mov .eax (argOp 0),
      .mov .ecx (argOp 1)] : List Instr)

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
