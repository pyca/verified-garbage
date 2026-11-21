module

public import VerifiedGarbage.Impl.AesOfb.X86

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
Decryption is around the block function with every implementation.

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

end VG.Impl.AesCfb.X86
