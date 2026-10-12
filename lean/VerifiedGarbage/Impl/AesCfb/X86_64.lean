module

public import VerifiedGarbage.Impl.AesOfb.X86_64

/-!
# AES-CFB128: x86-64 implementation

`vg_aes_cfb128_encrypt(schedule = rdi, rounds = rsi, iv = rdx, data = rcx, n = r8, scratch = r9)`
and `vg_aes_cfb128_decrypt` with the same arguments (see
`VG.Spec.Cfb.aesEncryptContract` and `aesDecryptContract`), composed of
calls of the verified `vg_aes_encrypt_blocks` on one block at a time. They
are generic over the implementation they call (`Blocks`): each is emitted
once for each implementation (e.g. `vg_aes_cfb128_encrypt_aesni` calls
`vg_aes_encrypt_blocks_aesni`).

They are built from AES-OFB's pieces (`Impl/AesOfb/X86_64.lean`), whose
arguments are the same: each block, the block at `iv` is enciphered in
place and XORed into the data block, as in OFB, and the block at `iv` then
becomes the ciphertext block:

* `encrypt`: the data block, now `Cⱼ`, copied to `iv`.
* `decrypt`: the data block, now `Pⱼ = Cⱼ ⊕ Oⱼ`, XORed into `iv`, which
  holds `Oⱼ`, leaving `Cⱼ` there.

Only the pointers, `rounds` and `n` can affect timing.
-/

@[expose] public section

namespace VG.Impl.AesCfb.X86_64

open VG.X86_64
open VG.Impl.Aes.X86_64 (Blocks)
open VG.Impl.AesCbc.X86_64 (whole xorInto copy advance)
open VG.Impl.AesOfb.X86_64 (ivArgs)

/-- One block: the block at `iv` enciphered in place, and `post`. -/
def body (b : Blocks) (post : List Instr) : Prog isa :=
  .seq (.block ivArgs) (.seq (.call b.name b.code) (.block post))

/-- `Cⱼ = Pⱼ ⊕ CIPH_K(Cⱼ₋₁)`, and `Cⱼ` the block to continue from. -/
def encPost : List Instr := xorInto .r13 .r12 ++ copy .r12 0 .r13 0 ++ advance

/-- `Pⱼ = Cⱼ ⊕ CIPH_K(Cⱼ₋₁)`, and `Cⱼ` the block to continue from. -/
def decPost : List Instr := xorInto .r13 .r12 ++ xorInto .r12 .r13 ++ advance

def encrypt (b : Blocks) : Prog isa := whole (body b encPost)

def decrypt (b : Blocks) : Prog isa := whole (body b decPost)

end VG.Impl.AesCfb.X86_64
