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

Decryption's inputs of the block cipher are all known in advance, so while
at least four blocks are left it takes them four at a time
(`Impl.AesCbc.X86_64.groups`, `decGroup`), by one call: `Cⱼ₋₁` for each
(the block at `iv` for the first, the data block before it for the others)
copied to the scratch buffer at `[2112, 2176)` (`gOff`) and enciphered there
in place, the last block `Cⱼ` copied to `iv`, and each enciphered block XORed
into its data block. The blocks left are decrypted one at a time as above.

Only the pointers, `rounds` and `n` can affect timing.
-/

@[expose] public section

namespace VG.Impl.AesCfb.X86_64

open VG.X86_64
open VG.Impl.Aes.X86_64 (Blocks)
open VG.Impl.AesCbc.X86_64 (whole xorInto copy advance gOff xorAt advance4 batched)
open VG.Impl.AesOfb.X86_64 (ivArgs)

/-- One block: the block at `iv` enciphered in place, and `post`. -/
def body (b : Blocks) (post : List Instr) : Prog isa :=
  .seq (.block ivArgs) (.seq (.call b.name b.code) (.block post))

/-- `Cⱼ = Pⱼ ⊕ CIPH_K(Cⱼ₋₁)`, and `Cⱼ` the block to continue from. -/
def encPost : List Instr := xorInto .r13 .r12 ++ copy .r12 0 .r13 0 ++ advance

/-- `Pⱼ = Cⱼ ⊕ CIPH_K(Cⱼ₋₁)`, and `Cⱼ` the block to continue from. -/
def decPost : List Instr := xorInto .r13 .r12 ++ xorInto .r12 .r13 ++ advance

def encrypt (b : Blocks) : Prog isa := whole (body b encPost)

/-- Data block `j` copied to slot `j + 1`. -/
def saveAt (j : Nat) : List Instr := copy .r15 (gOff + 16 * (j + 1)) .r13 (16 * j)

/-- `Cⱼ₋₁` of each of the four blocks at `r13` copied to `gOff`: the block at
`iv`, then the data blocks before the last. -/
def decSave : List Instr :=
  copy .r15 gOff .r12 0 ++ saveAt 0 ++ saveAt 1 ++ saveAt 2

/-- The arguments of the block function for the four blocks at `gOff`. -/
def callArgs4 : List Instr :=
  [.mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .rdx (.reg .r15),
   .alu .add .rdx (.imm (BitVec.ofNat 32 gOff)), .mov32 .rcx (.imm 4), .mov .r8 (.reg .r15)]

/-- Slot `j` XORed into data block `j`. -/
def fixAt (j : Nat) : List Instr := xorAt .r13 (16 * j) .r15 (gOff + 16 * j)

/-- The last `Cⱼ` copied to `iv`, and each `CIPH_K(Cⱼ₋₁)` XORed into its
data block. -/
def decFix : List Instr :=
  copy .r12 0 .r13 (16 * 3) ++ fixAt 0 ++ fixAt 1 ++ fixAt 2 ++ fixAt 3

/-- Four blocks: their inputs copied, enciphered by one call, and XORed in. -/
def decGroup (b : Blocks) : Prog isa :=
  .seq (.block (decSave ++ callArgs4)) (.seq (.call b.name b.code) (.block (decFix ++ advance4)))

def decrypt (b : Blocks) : Prog isa := batched (decGroup b) (body b decPost)

end VG.Impl.AesCfb.X86_64
