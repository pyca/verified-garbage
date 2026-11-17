module

public import VerifiedGarbage.Impl.AesOfb.Arm
public import VerifiedGarbage.Impl.AesCbc.Arm.Groups

/-!
# AES-CFB128: 32-bit ARM implementation

`vg_aes_cfb128_encrypt(schedule = r0, rounds = r1, iv = r2, data = r3, n = [sp], scratch = [sp + 4])`
and `vg_aes_cfb128_decrypt` with the same arguments (see
`VG.Spec.Cfb.aesEncryptContract` and `aesDecryptContract`), composed of
calls of the verified `vg_aes_encrypt_blocks`: on one block at a time, but
for decryption's groups (below).

They are built from AES-OFB's pieces (`Impl/AesOfb/Arm.lean`), whose
arguments are the same: each block, the block at `iv` (`r6`) is enciphered
in place and XORed into the data block (`r7`) a word at a time, as in OFB,
and the block at `iv` then becomes the ciphertext block:

* `encrypt`: the data block, now `Cⱼ`, copied to `iv` (zeroed, then XORed
  with it).
* `decrypt`: the data block, now `Pⱼ = Cⱼ ⊕ Oⱼ`, XORed into `iv`, which
  holds `Oⱼ`, leaving `Cⱼ` there.

Decryption's input blocks are ciphertext blocks, so it first takes the blocks
in groups of 4 and of 2, each one call of the block function (`cfbDecG`,
`Impl/AesCbc/Arm/Groups.lean`), and the blocks left one at a time.

Only the pointers, `rounds` and `n` can affect timing: the only branches are
on `n`.
-/

@[expose] public section

namespace VG.Impl.AesCfb.Arm

open VG.Arm
open VG.Impl.CmacAes.Arm (advance xor4)
open VG.Impl.AesCbc.Arm (whole wholeG cfbDecG groupLevels encFrame zero4)
open VG.Impl.AesOfb.Arm (ivArgs)

/-- One block: the block at `iv` enciphered in place, and `post`. -/
def body (post : List Instr) : Prog isa := .seq (.block ivArgs) (.seq encFrame (.block post))

/-- `Cⱼ = Pⱼ ⊕ CIPH_K(Cⱼ₋₁)`, and `Cⱼ` the block to continue from. -/
def encPost : List Instr := xor4 .r7 .r6 .r7 0 0 0 ++ zero4 .r6 0 ++ xor4 .r6 .r7 .r6 0 0 0 ++ advance

/-- `Pⱼ = Cⱼ ⊕ CIPH_K(Cⱼ₋₁)`, and `Cⱼ` the block to continue from. -/
def decPost : List Instr := xor4 .r7 .r6 .r7 0 0 0 ++ xor4 .r6 .r7 .r6 0 0 0 ++ advance

def encrypt : Prog isa := whole (body encPost)

def decrypt : Prog isa := wholeG encFrame cfbDecG groupLevels (body decPost)

end VG.Impl.AesCfb.Arm
