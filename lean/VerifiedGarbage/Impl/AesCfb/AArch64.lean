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

Decryption's inputs of the block cipher are all known in advance, so while
at least four blocks are left it takes them four at a time
(`Impl.AesCbc.AArch64.groups`, `decGroup`), by one call. The scratch buffer
has no room for four blocks in a row, so they are enciphered where the data
is: the four `Cⱼ` are saved as AES-CBC's decryption saves them (`decSave`:
the first three at `gOff`, the fourth at `cOff`), `Cⱼ₋₁` of each is copied
over its data block (the block at `iv` for the first, the saved block before
it for the others), the four are enciphered in place, each is XORed with its
saved `Cⱼ`, and the last saved `Cⱼ` is copied to `iv`. The blocks left are
decrypted one at a time as above.

Only the pointers, `rounds` and `n` can affect timing.
-/

@[expose] public section

namespace VG.Impl.AesCfb.AArch64

open VG.AArch64
open VG.Impl.Aes.AArch64 (Blocks)
open VG.Impl.AesCbc.AArch64 (whole xorInto copy advance gOff cOff xorAt advance4 batched decSave callArgs4)
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

/-- `Cⱼ` (in slot `j`) copied over data block `j + 1`, whose `Cⱼ₋₁` it is. -/
def inAt (j : Nat) : List Instr := copy .x22 (16 * (j + 1)) .x24 (gOff + 16 * j)

/-- `Cⱼ₋₁` of each of the four blocks at `x22` copied over it: the saved
blocks for the last three, the block at `iv` for the first. -/
def decIn : List Instr := inAt 0 ++ inAt 1 ++ inAt 2 ++ copy .x22 0 .x21 0

/-- The saved `Cⱼ` (in slot `j`) XORed into data block `j`. -/
def fixAt (j : Nat) : List Instr := xorAt .x22 (16 * j) .x24 (gOff + 16 * j)

/-- Each `CIPH_K(Cⱼ₋₁)` XORed with its saved `Cⱼ`, and the last `Cⱼ` copied
to `iv`. -/
def decFix : List Instr :=
  fixAt 0 ++ fixAt 1 ++ fixAt 2 ++ xorAt .x22 48 .x24 cOff ++ copy .x21 0 .x24 cOff

/-- Four blocks: saved, replaced by their inputs, enciphered by one call, and
XORed with the saved blocks. -/
def decGroup (b : Blocks) : Prog isa :=
  .seq (.block (decSave ++ decIn ++ callArgs4)) (.seq (.call b.name b.code) (.block (decFix ++ advance4)))

def decrypt (b : Blocks) : Prog isa := batched (decGroup b) (body b decPost)

end VG.Impl.AesCfb.AArch64
