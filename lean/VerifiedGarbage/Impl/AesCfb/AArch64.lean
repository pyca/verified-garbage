module

public import VerifiedGarbage.Impl.AesOfb.AArch64

/-!
# AES-CFB128: AArch64 implementation

`vg_aes_cfb128_encrypt(schedule = x0, rounds = x1, iv = x2, data = x3, n = x4, scratch = x5)`
and `vg_aes_cfb128_decrypt` with the same arguments (see
`VG.Spec.Cfb.aesEncryptContract` and `aesDecryptContract`), composed of
calls of the verified `vg_aes_encrypt_blocks` on one block at a time. They
are generic over the implementation they call (`Blocks`): each is emitted
once for each implementation (e.g. `vg_aes_cfb128_encrypt_aes` calls
`vg_aes_encrypt_blocks_aes`).

They are built from AES-OFB's pieces (`Impl/AesOfb/AArch64.lean`), whose
arguments are the same: each block, the block at `iv` (`x21`) is
enciphered in place and XORed into the data block (`x22`), as in OFB, and
the block at `iv` then becomes the ciphertext block:

* `encrypt`: the data block, now `Cⱼ`, copied to `iv`.
* `decrypt`: the data block, now `Pⱼ = Cⱼ ⊕ Oⱼ`, XORed into `iv`, which
  holds `Oⱼ`, leaving `Cⱼ` there.

Only the pointers, `rounds` and `n` can affect timing.
-/

@[expose] public section

namespace VG.Impl.AesCfb.AArch64

open VG.AArch64
open VG.Impl.Aes.AArch64 (Blocks)
open VG.Impl.AesCbc.AArch64 (whole xorInto copy advance)
open VG.Impl.AesOfb.AArch64 (ivArgs)

/-- The block at `x21` XORed with the data block at `x22`, in place. -/
def xorIv : List Instr :=
  [.ldr .x .x9 .x21 0, .ldr .x .x10 .x22 0, .logic .eor .x .x9 .x9 .x10, .str .x .x9 .x21 0,
   .ldr .x .x9 .x21 8, .ldr .x .x10 .x22 8, .logic .eor .x .x9 .x9 .x10, .str .x .x9 .x21 8]

/-- One block: the block at `iv` enciphered in place, and `post`. -/
def body (b : Blocks) (post : List Instr) : Prog isa :=
  .seq (.block ivArgs) (.seq (.call b.name b.code) (.block post))

/-- `Cⱼ = Pⱼ ⊕ CIPH_K(Cⱼ₋₁)`, and `Cⱼ` the block to continue from. -/
def encPost : List Instr := xorInto ++ copy .x21 0 .x22 0 ++ advance

/-- `Pⱼ = Cⱼ ⊕ CIPH_K(Cⱼ₋₁)`, and `Cⱼ` the block to continue from. -/
def decPost : List Instr := xorInto ++ xorIv ++ advance

def encrypt (b : Blocks) : Prog isa := whole (body b encPost)

def decrypt (b : Blocks) : Prog isa := whole (body b decPost)

end VG.Impl.AesCfb.AArch64
