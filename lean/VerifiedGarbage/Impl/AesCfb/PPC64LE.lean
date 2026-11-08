module

public import VerifiedGarbage.Impl.AesOfb.PPC64LE

/-!
# AES-CFB128: PPC64LE implementation

`vg_aes_cfb128_encrypt(schedule = r3, rounds = r4, iv = r5, data = r6, n = r7, scratch = r8)`
and `vg_aes_cfb128_decrypt` with the same arguments (see
`VG.Spec.Cfb.aesEncryptContract` and `aesDecryptContract`), composed of
calls of the verified `vg_aes_encrypt_blocks` on one block at a time, as on
x86-64 (`VG.Impl.AesCfb.X86_64`).

They are built from AES-OFB's pieces (`Impl/AesOfb/PPC64LE.lean`), whose
arguments are the same: each block, the block at `iv` is enciphered in
place and XORed into the data block, as in OFB, and the block at `iv` then
becomes the ciphertext block:

* `encrypt`: the data block, now `Cⱼ`, copied to `iv`.
* `decrypt`: the data block, now `Pⱼ = Cⱼ ⊕ Oⱼ`, XORed into `iv`, which
  holds `Oⱼ`, leaving `Cⱼ` there.

Decryption's inputs of the block cipher are all known in advance, so while
at least eight blocks are left it takes them eight at a time
(`Impl.AesCbc.PPC64LE.groups`, `decGroup`), by one call: `Cⱼ₋₁` of each (the
block at `iv` for the first, the data block before it for the others)
copied to the slots at the start of the scratch buffer and enciphered there
in place (with the working space after them), the last block `Cⱼ` copied to
`iv`, and each enciphered slot XORed into its data block. The blocks left
are decrypted one at a time as above.

Only the pointers, `rounds` and `n` can affect timing.
-/

@[expose] public section

namespace VG.Impl.AesCfb.PPC64LE

open VG.PPC64LE
open VG.Impl.AesCbc.PPC64LE (whole xorInto copy advance encCall mov slot saveSlots fixSlots advance8 batched)
open VG.Impl.AesOfb.PPC64LE (ivArgs)

/-- One block: the block at `iv` enciphered in place, and `post`. -/
def body (post : List Instr) : Prog isa := .seq (.block ivArgs) (.seq encCall (.block post))

/-- `Cⱼ = Pⱼ ⊕ CIPH_K(Cⱼ₋₁)`, and `Cⱼ` the block to continue from. -/
def encPost : List Instr := xorInto .r17 .r16 ++ copy .r16 0 .r17 0 ++ advance

/-- `Pⱼ = Cⱼ ⊕ CIPH_K(Cⱼ₋₁)`, and `Cⱼ` the block to continue from. -/
def decPost : List Instr := xorInto .r17 .r16 ++ xorInto .r16 .r17 ++ advance

def encrypt : Prog isa := whole (body encPost)

/-- The arguments of the block function for the eight slots at the start of
the scratch buffer, with the working space after them. -/
def callArgs8 : List Instr := [mov .r3 .r14, mov .r4 .r15, mov .r5 .r19, .li .r6 8, .addi .r7 .r19 128]

/-- Eight blocks: `Cⱼ₋₁` of each copied to slot `j` (the block at `iv` for the
first), the slots enciphered in place by one call, the last `Cⱼ` copied to
`iv`, and each slot XORed into its block. -/
def decGroup : Prog isa :=
  .seq (.block (saveSlots 7 ++ callArgs8))
    (.seq encCall (.block (copy .r16 0 .r17 (16 * 7) ++ fixSlots ++ advance8)))

def decrypt : Prog isa := batched decGroup (body decPost)

end VG.Impl.AesCfb.PPC64LE
