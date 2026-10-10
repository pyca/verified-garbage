import VerifiedGarbage.Impl.AesOfb.X86

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

Only the pointers, `rounds` and `n` can affect timing: the only branches are
on `n`.
-/

namespace VG.Impl.AesCfb.X86

open VG.X86
open VG.Impl.Aes.X86 (Blocks)
open VG.Impl.CmacAes.X86 (argOp advance xor4 zero4)
open VG.Impl.AesCbc.X86 (whole blkCall)
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

end VG.Impl.AesCfb.X86
