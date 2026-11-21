module

public import VerifiedGarbage.Impl.AesOfb.X86
public import VerifiedGarbage.Impl.Aes.X86.AesNiBlocks

/-!
# AES-CFB128: x86 (32-bit) implementation

`vg_aes_cfb128_encrypt(schedule, rounds, iv, data, n, scratch)` and
`vg_aes_cfb128_decrypt` with the same arguments (see
`VG.Spec.Cfb.aesEncryptContract` and `aesDecryptContract`), every argument
on the stack (cdecl), composed of calls of the verified
`vg_aes_encrypt_blocks` on one block at a time. They are generic over the
implementation they call (`Blocks`): each is emitted once for each
implementation (e.g. `vg_aes_cfb128_encrypt_aesni` calls
`vg_aes_encrypt_blocks_aesni`).

They are built from AES-OFB's pieces (`Impl/AesOfb/X86.lean`), whose
arguments are the same: each block, the block at `iv` is enciphered in
place and XORed into the data block (at `esi`) a word at a time, as in OFB,
and the block at `iv` then becomes the ciphertext block:

* `encrypt`: the data block, now `Cⱼ`, copied to `iv` (zeroed, then XORed
  with it).
* `decrypt`: the data block, now `Pⱼ = Cⱼ ⊕ Oⱼ`, XORed into `iv`, which
  holds `Oⱼ`, leaving `Cⱼ` there.

With AES-NI, encryption is not around the block function (`encryptNi`): as
AES-OFB has it (`Impl.AesOfb.X86.cryptNi`), the block at `iv` is loaded
into `xmm0` once; each block, it is enciphered there with no call
(`Impl.Aes.X86.AesNi.aes`, the round keys through `xmm6`) and XORed with
the data block (through `xmm7`), which leaves the ciphertext block in
`xmm0`, stored over the data block and enciphered for the next one; the
last is stored at `iv` once. It uses no stack, and of the scratch buffer it
writes only where it saves the registers, which it zeroes before returning.

Decryption with AES-NI calls nothing either (`decryptNi`): its blocks do not
depend on each other (each is the encipherment of the ciphertext block
before it, XORed with its own), so they are enciphered six at a time, as
`vg_aes_encrypt_blocks_aesni` does (`Impl/Aes/X86/AesNiBlocks.lean`): the
block at `iv` and the first five ciphertext blocks of a turn into
`xmm0`–`xmm5`, the sixth to `iv` (through `xmm7`), the six enciphered
together, and each XORed with its own ciphertext block (through `xmm7`) and
stored over it. The blocks left after the turns of six, five at most, are a
group of three, a group of two and one block, each taken once if that many
are left, in registers apart from each other (`regs3`, `regs2`, `regs1`), as
that function's are and for its reason: where the processor keeps the
registers' upper halves, a load into a register waits for the value the
register had. `edi` holds the number of blocks left (after the group of
three, the number left then).

Only the pointers, `rounds` and `n` can affect timing: the only branches are
on `n` and, with AES-NI, on `rounds`.
-/

@[expose] public section

namespace VG.Impl.AesCfb.X86

open VG.X86
open VG.Impl.Aes.X86 (Blocks)
open VG.Impl.CmacAes.X86 (argOp at_ advance xor4 zero4 setup restore niPre niPost)
open VG.Impl.AesCbc.X86 (whole blkCall zeroSaved)
open VG.Impl.AesOfb.X86 (ivArgs)
open VG.Impl.Aes.X86.AesNi (loadData regs6 regs3 regs2 regs1)

/-- One block: the block at `iv` enciphered in place, and `post`. -/
def body (b : Blocks) (post : List Instr) : Prog isa := .seq (.block ivArgs) (.seq (blkCall b) (.block post))

/-- `Cⱼ = Pⱼ ⊕ CIPH_K(Cⱼ₋₁)`, and `Cⱼ` the block to continue from. -/
def encPost : List Instr :=
  ([.mov .ebx (argOp 2)] : List Instr) ++ xor4 .esi .ebx .esi 0 0 0 ++ zero4 .ebx 0 ++ xor4 .ebx .esi .ebx 0 0 0 ++ advance

/-- `Pⱼ = Cⱼ ⊕ CIPH_K(Cⱼ₋₁)`, and `Cⱼ` the block to continue from. -/
def decPost : List Instr :=
  ([.mov .ebx (argOp 2)] : List Instr) ++ xor4 .esi .ebx .esi 0 0 0 ++ xor4 .ebx .esi .ebx 0 0 0 ++ advance

def encrypt (b : Blocks) : Prog isa := whole (body b encPost)

def decrypt (b : Blocks) : Prog isa := whole (body b decPost)

/-- One block of encryption with AES-NI: the last ciphertext block in `xmm0`
enciphered there (the round keys through `xmm6`) and XORed with the block
at `esi` (through `xmm7`), which gives the next ciphertext block, stored
over it, and on to the next block; ZF is set when none is left. -/
def encNiBody : Prog isa :=
  .seq (Impl.Aes.X86.AesNi.aes [.xmm0])
    (.block [.movdquLoad .xmm7 (at_ .esi 0), .xop (.bin .pxor .xmm0 .xmm7), .movdquStore (at_ .esi 0) .xmm0,
      .alu .add .esi (.imm 16), .alu .sub .edi (.imm 1)])

/-- `vg_aes_cfb128_encrypt` with AES-NI: the block at `iv` loaded into
`xmm0`, the blocks, and the last ciphertext block stored at `iv`, leaving
the scratch buffer as it was but for the zeros where it saved the
registers. -/
def encryptNi : Prog isa :=
  .seq (.block setup)
    (.seq (.ite .e (.block []) (.seq (.block niPre) (.seq (.loop encNiBody .ne) (.block niPost))))
      (.block (restore 5 ++ zeroSaved)))

/-- The cipher's inputs of the blocks at `esi` into the registers: the block
at `iv` (`edx`) into the first, each block but the last into the next
register, and the last block to `iv` (through `xmm7`), for the blocks after
these. -/
def decNiLoad : List XReg → List Instr
  | [] => []
  | b :: bs =>
    .movdquLoad b (at_ .edx 0) :: (loadData .esi bs 0 ++
      [.movdquLoad .xmm7 (at_ .esi (16 * bs.length)), .movdquStore (at_ .edx 0) .xmm7])

/-- `Pⱼ = Cⱼ ⊕ CIPH_K(Cⱼ₋₁)` for each register, from block `j` on: the
ciphertext block into `xmm7`, XORed into the register, which is stored over
it. -/
def decNiXor : List XReg → Nat → List Instr
  | [], _ => []
  | b :: bs, j =>
    [.movdquLoad .xmm7 (at_ .esi (16 * j)), .xop (.bin .pxor b .xmm7), .movdquStore (at_ .esi (16 * j)) b] ++
      decNiXor bs (j + 1)

/-- The blocks at `esi` deciphered in the registers `rs`; then `rest`. -/
def decNiGroup (rs : List XReg) (rest : List Instr) : Prog isa :=
  .seq (.block (decNiLoad rs)) (.seq (Impl.Aes.X86.AesNi.aes rs) (.block (decNiXor rs 0 ++ rest)))

/-- Six blocks. -/
def decNi6 : Prog isa :=
  decNiGroup regs6 [.alu .add .esi (.imm 96), .alu .sub .edi (.imm 6), .alu .cmp .edi (.imm 6)]

/-- Three blocks, if three are left. -/
def decNi3 : Prog isa :=
  .seq (.block [.alu .cmp .edi (.imm 3)])
    (.ite .b (.block []) (decNiGroup regs3 [.alu .add .esi (.imm 48), .alu .sub .edi (.imm 3)]))

/-- The blocks at `esi` in the registers `rs`, if the number of blocks in
`edi` has the bit `rs.length` (2 or 1); then `esi` past them. -/
def decNiBit (rs : List XReg) : Prog isa :=
  .seq (.block [.alu .test .edi (.imm (BitVec.ofNat 32 rs.length))])
    (.ite .e (.block []) (decNiGroup rs [.alu .add .esi (.imm (BitVec.ofNat 32 (16 * rs.length)))]))

/-- The number of blocks, the schedule, `rounds` and `iv` into `edi`, `eax`,
`ecx` and `edx`; CF is set if fewer than six blocks are left. -/
def decNiPre : List Instr :=
  [.mov .edi (argOp 4), .mov .eax (argOp 0), .mov .ecx (argOp 1), .mov .edx (argOp 2),
   .alu .cmp .edi (.imm 6)]

/-- The blocks, six at a time, and then three, two and one, after
`cmp edi, 6`. -/
def decNiTail : Prog isa :=
  .seq (.ite .b (.block []) (.loop decNi6 .ae)) (.seq decNi3 (.seq (decNiBit regs2) (decNiBit regs1)))

/-- What `decryptNi` runs when there are blocks. -/
def decNiMid : Prog isa := .seq (.block decNiPre) decNiTail

/-- `vg_aes_cfb128_decrypt` with AES-NI: the blocks, leaving the last
ciphertext block at `iv`, and the scratch buffer as it was but for the zeros
where it saved the registers. -/
def decryptNi : Prog isa :=
  .seq (.block setup) (.seq (.ite .e (.block []) decNiMid) (.block (restore 5 ++ zeroSaved)))

end VG.Impl.AesCfb.X86
